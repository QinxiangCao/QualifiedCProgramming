From Coq Require Import ZArith List String Lia.
From AUXLib Require Import ListLib.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From MonadLib.MonadErr Require Import StateRelMonadErr.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

(* 本文件所有 monad 程序统一使用这一种带错误的关系式 monad。
   隐式状态为 unit；真正的 RC map 仍显式传入并作为返回值传出。
   nrm 表示正常返回（包括 C 返回失败码），err 表示容量检查失败。
   MonadNotation 的 <-、;;、ret 都通过同一个 MonadErr 实例解释。 *)
Notation RCProgram := (MonadErr.M unit).

(* 公开的语义观察：返回值和错误；unit 仅为所用 monad 的隐式状态。
   程序体仍统一用 ret、<-、;; 编写，不把语义投影当成第二种 monad。 *)
Definition rc_returns {A : Type} (c : RCProgram A) (a : A) : Prop :=
  MonadErr.nrm c tt a tt.
Definition rc_errors {A : Type} (c : RCProgram A) : Prop :=
  MonadErr.err c tt.

(* Generic layer: RCMap is a finite, acyclic rooted graph ledger, independent
   of any syntax or C layout. RC_PAYLOAD_SIG supplies nodes and owning edges;
   RCMAP_SIG describes implementations, MakeRCMap supplies the default one,
   and RCMapFacts proves interface-level laws. Multiplicity counts edges,
   not copies of a physical points-to permission. Concrete decoders and
   ownership predicates belong in each client's instance module. *)

(* A generic finite, rooted reference-counted map.  Finite support is a
   proposition, never a stored Live_keys list.  The payload interface records
   owning edges as a list, so two equal child addresses count twice. *)
Module RCMap.
Section Generic.
Context {N : Type}.
Variable children : N -> list addr.

(* N 只描述一个节点的一层内容；children 列出该节点拥有的出边。
   必须用 list 而不是集合：若左右孩子都是 q，就确实有两条 owning 引用。
   非 owning 的借用指针不应放进 children。 *)
Record t := make {
  (* 地址到单层 payload；None 表示该地址不在当前活节点图中。 *)
  nodes : addr -> option N;
  (* 来自图外的 owning 引用数，如 solution 槽位和临时保留的引用。
     不是所有 C 局部指针的个数：借用/别名本身不会增加它。 *)
  roots : addr -> Z;
  (* C 节点 refcnt 字段的逻辑镜像：roots + 图内入边数。 *)
  counts : addr -> Z;
  (* Owning-root credits not handed to an external container.  This is
     accounting metadata, NOT a second physical reference counter. *)
  (* roots 中尚未交给外部容器的部分，例如 retain 的临时引用、删除父节点后
     等待 release 的子引用。它已计入 roots，不能再加到 counts 上。
     roots - reserved 才是可供 solution 槽位核对的引用预算。 *)
  reserved : addr -> Z
}.

(* es 是有限性的证明见证：恰好列出所有活节点且地址不重复。
   它存在于 Prop 中，不要求程序能枚举它，因此无需存储 Live_keys。 *)
Definition entries (M : t) (es : list (addr * N)) : Prop :=
  NoDup (map fst es) /\
  forall p n, In (p,n) es <-> nodes M p = Some n.

(* 统计所有节点指向 p 的 owning 边，重复孩子按出现次数计算。 *)
Definition incoming (es : list (addr * N)) (p : addr) : Z :=
  Z.of_nat (count_occ Z.eq_dec
    (List.concat (map (fun e => children (snd e)) es)) p).

(* 总账恒等式；同时要求图有限。counts 并非一个可任意指定的上界。 *)
Definition exact (M : t) : Prop :=
  exists es, entries M es /\
    forall p, counts M p = roots M p + incoming es p.

(* 每条 owning 出边都指向活节点，排除悬空孩子。 *)
Definition closed (M : t) : Prop :=
  forall p n q, nodes M p = Some n -> In q (children n) ->
    exists nq, nodes M q = Some nq.

(* rank 是无环性的证明见证，不是 C 字段。沿边严格下降且活节点 rank 非负。
   允许 DAG 共享，但当前方案不覆盖带环引用图的回收。 *)
Definition acyclic (M : t) : Prop :=
  exists rank : addr -> Z,
    (forall p n, nodes M p = Some n -> 0 <= rank p) /\
    forall p n q, nodes M p = Some n -> In q (children n) ->
      rank q < rank p.

(* 将账目一致、闭合、无环、非负根数、活节点非空且计数不溢出、
   死节点账目归零，以及 reserved 属于 roots，集中为一个纯不变量。
   valid 本身不拥有任何堆；后面的 store_world 也不自动包含 valid。 *)
Definition valid (M : t) : Prop :=
  exact M /\ closed M /\ acyclic M /\
  (forall p, 0 <= roots M p) /\
  (forall p n, nodes M p = Some n -> p <> 0 /\ 0 < counts M p <= 2147483647) /\
  (forall p, nodes M p = None -> counts M p = 0 /\ roots M p = 0) /\
  (forall p, 0 <= reserved M p <= roots M p).

(* 函数式单点更新工具，不读写 C 内存。 *)
Definition put_count (f : addr -> Z) (p : addr) (z : Z) :=
  fun q => if Z.eq_dec p q then z else f q.

(* 保留一个临时 owning 引用：非空地址的 roots/counts/reserved 一起 +1。
   所以 retain 不会增加 solution 可使用的 roots - reserved。
   注意下面这些纯变换可应用于任意 M；安全性来自引理/调用规格的前提，
   不是定义自带检查。例如 retain_valid 还要求节点存在且计数有余量。 *)
Definition retain (M : t) (p : addr) : t :=
  if Z.eq_dec p 0 then M else
  make (nodes M) (put_count (roots M) p (roots M p + 1))
    (put_count (counts M) p (counts M p + 1))
    (put_count (reserved M) p (reserved M p + 1)).

(* Transfer one retained owning reference to an external container.  This
   changes no physical pointer or count, only which root account owns it. *)
(* 把一个临时引用交给容器：只将 reserved 减一，counts 不变。
   对应 add_map 接收已经 retain 的引用；需要确实有 reserved 可交付。 *)
Definition publish (M : t) (p : addr) : t :=
  make (nodes M) (roots M) (counts M)
    (put_count (reserved M) p (reserved M p - 1)).

(* 最后一个引用被释放时，删除父节点 p 的账目，并将它的每条子边转为
   子节点的临时根引用：子节点的 roots/reserved 增加，counts 暂时不变。
   原因是此刻只删除了父节点；孩子要在后续 release 中逐个处理。
   例如孩子列表 [q;q] 产生两个待释放引用，不能去重。
   这个定义不检查 n 是否为 p 的 payload，也不检查是否为最后一个引用；
   应用它的证明必须提供这些条件。 *)
Definition delete (M : t) (p : addr) (n : N) : t :=
  make
    (fun q => if Z.eq_dec p q then None else nodes M q)
    (fun q => if Z.eq_dec p q then 0 else roots M q +
       Z.of_nat (count_occ Z.eq_dec (children n) q))
    (put_count (counts M) p 0)
    (fun q => if Z.eq_dec p q then 0 else reserved M q +
       Z.of_nat (count_occ Z.eq_dec (children n) q)).

(* 非最后一个引用：消耗一个临时根，roots/counts/reserved 一起 -1。
   节点及子边不变；安全调用还需有临时根可消耗且计数大于一。 *)
Definition decrement (M : t) (p : addr) : t :=
  make (nodes M) (put_count (roots M) p (roots M p - 1))
    (put_count (counts M) p (counts M p - 1))
    (put_count (reserved M) p (reserved M p - 1)).

(* Deleting a last-reference parent turns its owning child edges into
   temporary roots.  No physical child count changes until its recursive
   release.  Repeated edges create repeated temporary roots. *)
(* jobs 是待释放引用的工作列表，M 是当前账本，W 是递归调用占位符。
   删除父节点后把 children 接到 jobs 前面；因此重复边会执行多次 release。
   None 分支只是抽象程序的定义，不表示 C 可以安全释放任意无效地址；
   C 证明必须另外排除非法调用。
   这是关系式 monad 程序：递归由 Rec 的不动点语义给出，而非要求对 M
   进行可计算遍历。图状态以普通参数传入，并作为返回值传出。 *)
Definition release_rec
    (W : (list addr * t) -> RCProgram t) (arg : list addr * t) : RCProgram t :=
  let '(jobs,M) := arg in
  match jobs with
  | [] => ret M
  | p :: tail =>
      if Z.eq_dec p 0 then W (tail,M) else
      match nodes M p with
      | None => W (tail,M)
      | Some n =>
          if Z.eq_dec (counts M p) 1
          then W (children n ++ tail, delete M p n)
          else W (tail, decrement M p)
      end
  end.

(* 对外从单个待释放地址开始；返回的仍是更新后的 map。 *)
Definition release_program (M : t) (p : addr) : RCProgram t :=
  Rec release_rec ([p],M).

(* 在纯 retain 变换外增加容量检查；assert 失败进入 monad 的 err 分量。
   这个检查不代替 valid、节点存在性或内存权限。 *)
Definition retain_program (M : t) (p : addr) : RCProgram t :=
  assert (p = 0 \/ counts M p < 2147483647) ;;
  ret (retain M p).

(* 相对基准 B 的保留关系：旧节点 payload 不变，旧根引用数不减少。
   用来说明推理过程不会破坏调用者借用的旧类型；不要求 counts 或 reserved
   相等。一般的 release 并不满足它；清理临时引用时需证明仍保留基准 B。 *)
Definition preserves (B M : t) : Prop :=
  (forall p n, nodes B p = Some n -> nodes M p = Some n) /\
  (forall p, roots B p <= roots M p).

Lemma preserves_refl : forall M, preserves M M.
Proof. unfold preserves; intro M; split; [auto | intro p; lia]. Qed.

Lemma preserves_trans : forall A B C,
  preserves A B -> preserves B C -> preserves A C.
Proof.
  unfold preserves; intros A B C [Hab Rab] [Hbc Rbc].
  split; [eauto | intro p; specialize (Rab p); specialize (Rbc p); lia].
Qed.

Lemma retain_preserves : forall M p, preserves M (retain M p).
Proof.
  intros M p; unfold retain; destruct (Z.eq_dec p 0).
  - apply preserves_refl.
  - split; cbn; [auto | intro q; unfold put_count;
      destruct (Z.eq_dec p q) as [->|Hne]; lia].
Qed.

Lemma retain_valid : forall M p,
  valid M ->
  (p = 0 \/ (exists n, nodes M p = Some n) /\ counts M p < 2147483647) ->
  valid (retain M p).
Proof.
  intros M p Hv Hcap; unfold retain.
  destruct (Z.eq_dec p 0) as [Hz|Hz]; [exact Hv|].
  destruct Hv as [Hex [Hclosed [Hacyclic [Hr [Hlive [Hdead Hreserved]]]]]].
  destruct Hcap as [Hcap|[[n Hnode] Hcap]]; [contradiction|].
  split.
  - destruct Hex as [es [Hes Hcount]]. exists es; split; [exact Hes|].
    intro q; cbn; unfold put_count; destruct (Z.eq_dec p q); subst; specialize (Hcount q); lia.
  - split; [exact Hclosed|]. split; [exact Hacyclic|].
    split.
    + intro q; cbn; unfold put_count; destruct (Z.eq_dec p q); subst; specialize (Hr q); lia.
    + split.
      * intros q nq Hq; cbn in Hq |- *; unfold put_count.
        destruct (Z.eq_dec p q); subst; specialize (Hlive q nq Hq); lia.
      * split.
        -- intros q Hq; cbn in Hq |- *; unfold put_count.
           destruct (Z.eq_dec p q); subst; [rewrite Hnode in Hq; discriminate|auto].
        -- intro q; cbn; unfold put_count; specialize (Hreserved q).
           destruct (Z.eq_dec p q); subst; lia.
Qed.

Lemma release_rec_mono_cont : mono_cont release_rec.
Proof. unfold release_rec; mono_cont_auto. Qed.

Lemma publish_valid : forall M p,
  valid M -> 0 < reserved M p -> valid (publish M p).
Proof.
  intros M p [Hex [Hcl [Hac [Hr [Hl [Hd Hres]]]]]] Hp.
  split; [exact Hex|]. split; [exact Hcl|]. split; [exact Hac|].
  split; [exact Hr|]. split; [exact Hl|]. split; [exact Hd|].
  intro q; cbn; unfold put_count; specialize (Hres q).
  destruct (Z.eq_dec p q); subst; lia.
Qed.

Lemma retain_available : forall M p q,
  roots (retain M p) q - reserved (retain M p) q = roots M q - reserved M q.
Proof.
  intros; unfold retain; destruct (Z.eq_dec p 0); [reflexivity|].
  cbn; unfold put_count; destruct (Z.eq_dec p q); subst; lia.
Qed.

Lemma decrement_available : forall M p q,
  roots (decrement M p) q - reserved (decrement M p) q = roots M q - reserved M q.
Proof.
  intros; cbn; unfold put_count; destruct (Z.eq_dec p q); subst; lia.
Qed.

Lemma publish_retained_reservations : forall M p,
  p <> 0 -> forall q, reserved (publish (retain M p) p) q = reserved M q.
Proof.
  intros M p Hp q; unfold publish, retain; destruct (Z.eq_dec p 0); [contradiction|].
  cbn; unfold put_count; destruct (Z.eq_dec p p); [|contradiction].
  destruct (Z.eq_dec p q); subst; lia.
Qed.

Lemma release_nrm_unfold : forall jobs M M',
  MonadErr.nrm (Rec release_rec (jobs,M)) tt M' tt <->
  MonadErr.nrm (release_rec (Rec release_rec) (jobs,M)) tt M' tt.
Proof.
  intros jobs M M'.
  pose proof (Rec_unfold release_rec release_rec_mono_cont) as H.
  destruct (H (jobs,M)) as [Hn He]. apply Hn.
Qed.

End Generic.
Arguments make {N}.
Arguments nodes {N}.
Arguments roots {N}.
Arguments counts {N}.
Arguments reserved {N}.
End RCMap.

(* 真正的模块接口；这里的 Parameter 是模块实现必须提供的字段，
   不是可被具体实例直接使用的全局公理。两种 payload 的具体模块在后文。
   node 只描述一层内容；children 明确哪些地址是 owning 引用。 *)
Module Type RC_PAYLOAD_SIG.
  Parameter node : Type.
  Parameter children : node -> list addr.
End RC_PAYLOAD_SIG.

Module Type RCMAP_SIG (P : RC_PAYLOAD_SIG).
  (* state 可不同于 kernel 的函数式账本；view 是完整的逻辑观察。 *)
  Parameter state : Type.
  Parameter view : state -> @RCMap.t P.node.

  (* 纯状态变换不进行检查，也不读写实际 C 内存。规律逐一规定它们
     如何改变观察结果，保留重复边与 reserved 的既有语义。 *)
  Parameter retain : state -> addr -> state.
  Parameter publish : state -> addr -> state.
  Parameter delete : state -> addr -> P.node -> state.
  Parameter decrement : state -> addr -> state.
  Parameter retain_view : forall M p,
    view (retain M p) = RCMap.retain (view M) p.
  Parameter publish_view : forall M p,
    view (publish M p) = RCMap.publish (view M) p.
  Parameter delete_view : forall M p n,
    view (delete M p n) = RCMap.delete P.children (view M) p n.
  Parameter decrement_view : forall M p,
    view (decrement M p) = RCMap.decrement (view M) p.

  (* 与纯变换分开：程序使用统一 RCProgram，M 仍是输入/返回值。
     nrm/err 两部分都受规律约束，不能用“总是报错”伪装正确实现。 *)
  Parameter retain_program : state -> addr -> RCProgram state.
  Parameter release_program : state -> addr -> RCProgram state.
  (* 按观察后的输出给出 iff：既不允许伪造结果，也不能遗漏 kernel 的
     正常结果。view 不要求单射，允许实现状态额外带缓存等表示信息。 *)
  Parameter retain_nrm : forall M p V,
    (exists M', rc_returns (retain_program M p) M' /\ view M' = V) <->
    rc_returns (RCMap.retain_program (view M) p) V.
  Parameter retain_err : forall M p,
    rc_errors (retain_program M p) <->
    rc_errors (RCMap.retain_program (view M) p).
  Parameter release_nrm : forall M p V,
    (exists M', rc_returns (release_program M p) M' /\ view M' = V) <->
    rc_returns (RCMap.release_program P.children (view M) p) V.
  Parameter release_err : forall M p,
    rc_errors (release_program M p) <->
    rc_errors (RCMap.release_program P.children (view M) p).

(* 观察器和不变量由同一个 view 取得；无需再要求每个 instance 重新定义
   “有限”“无环”“总计数”等概念。valid 本身仍不包含任何堆权限。 *)
  Definition nodes (M : state) := RCMap.nodes (view M).
  Definition roots (M : state) := RCMap.roots (view M).
  Definition counts (M : state) := RCMap.counts (view M).
  Definition reserved (M : state) := RCMap.reserved (view M).
  Definition valid (M : state) := RCMap.valid P.children (view M).
  Definition preserves (B M : state) := RCMap.preserves (view B) (view M).
End RCMAP_SIG.

(* 默认实现：透明约束 <: 检查全部签名字段，但保留具体表示的可展开性。
   参数仅来自 payload 模块；每条 law 都在此证明，不引入额外假设。 *)
Module MakeRCMap (P : RC_PAYLOAD_SIG) <: RCMAP_SIG P.
  Definition state := @RCMap.t P.node.
  Definition view (M : state) := M.
  Definition retain := @RCMap.retain P.node.
  Definition publish := @RCMap.publish P.node.
  Definition delete := RCMap.delete P.children.
  Definition decrement := @RCMap.decrement P.node.
  Lemma retain_view : forall M p, view (retain M p) = RCMap.retain (view M) p.
  Proof. reflexivity. Qed.
  Lemma publish_view : forall M p, view (publish M p) = RCMap.publish (view M) p.
  Proof. reflexivity. Qed.
  Lemma delete_view : forall M p n,
    view (delete M p n) = RCMap.delete P.children (view M) p n.
  Proof. reflexivity. Qed.
  Lemma decrement_view : forall M p,
    view (decrement M p) = RCMap.decrement (view M) p.
  Proof. reflexivity. Qed.
  Definition retain_program := @RCMap.retain_program P.node.
  Definition release_program := RCMap.release_program P.children.
  Lemma retain_nrm : forall M p V,
    (exists M', rc_returns (retain_program M p) M' /\ view M' = V) <->
    rc_returns (RCMap.retain_program (view M) p) V.
  Proof.
    intros; split; [intros [M' [H Heq]]; unfold view in Heq; subst V; exact H |].
    intro H; exists V; split; [exact H | reflexivity].
  Qed.
  Lemma retain_err : forall M p,
    rc_errors (retain_program M p) <->
    rc_errors (RCMap.retain_program (view M) p).
  Proof. reflexivity. Qed.
  Lemma release_nrm : forall M p V,
    (exists M', rc_returns (release_program M p) M' /\ view M' = V) <->
    rc_returns (RCMap.release_program P.children (view M) p) V.
  Proof.
    intros; split; [intros [M' [H Heq]]; unfold view in Heq; subst V; exact H |].
    intro H; exists V; split; [exact H | reflexivity].
  Qed.
  Lemma release_err : forall M p,
    rc_errors (release_program M p) <->
    rc_errors (RCMap.release_program P.children (view M) p).
  Proof. reflexivity. Qed.
  Definition nodes (M : state) := RCMap.nodes (view M).
  Definition roots (M : state) := RCMap.roots (view M).
  Definition counts (M : state) := RCMap.counts (view M).
  Definition reserved (M : state) := RCMap.reserved (view M).
  Definition valid (M : state) := RCMap.valid P.children (view M).
  Definition preserves (B M : state) := RCMap.preserves (view B) (view M).
End MakeRCMap.

(* 接口使用者的证明只需接口规律，不需知道 state 的具体表示。 *)
Module RCMapFacts (P : RC_PAYLOAD_SIG) (I : RCMAP_SIG P).
Lemma retain_valid : forall M p,
  I.valid M ->
  (p = 0 \/ (exists n, I.nodes M p = Some n) /\ I.counts M p < 2147483647) ->
  I.valid (I.retain M p).
Proof.
  intros M p Hv Hcap.
  unfold I.valid; rewrite I.retain_view.
  apply RCMap.retain_valid; assumption.
Qed.

Lemma retain_preserves : forall M p, I.preserves M (I.retain M p).
Proof.
  intros; unfold I.preserves; rewrite I.retain_view.
  apply RCMap.retain_preserves.
Qed.

Lemma publish_valid : forall M p,
  I.valid M -> 0 < I.reserved M p -> I.valid (I.publish M p).
Proof.
  intros M p Hv Hr; unfold I.valid; rewrite I.publish_view.
  apply RCMap.publish_valid; assumption.
Qed.

Lemma retain_available : forall M p q,
  I.roots (I.retain M p) q - I.reserved (I.retain M p) q =
  I.roots M q - I.reserved M q.
Proof.
  intros; unfold I.roots, I.reserved; rewrite I.retain_view.
  apply RCMap.retain_available.
Qed.
End RCMapFacts.


