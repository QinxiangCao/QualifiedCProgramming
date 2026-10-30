# RCMAP_SIG：Module Type 版本的接口与设计说明

当前路线是 **Module Type + 实现 functor + 具体模块**，不是 TypeClass，也不再使用带证明 Record `RCMapSig`。2026-10-27 按用户要求拆为三层：

- [SeparationLogic/RCMap.v](../../../SeparationLogic/RCMap.v)：通用 RC 账本、模块接口、实现 functor 和通用性质，不依赖 typeinfer 的数学类型或 C 节点布局。
- [typeinfer_rc.v](./typeinfer_rc.v)：具体 type 实例、存储谓词、实例性质，以及字段 missing 接口与其通用拆合引理；本 case 的策略证明依赖这一层。
- [typeinfer_rc_lib.v](./typeinfer_rc_lib.v)：导出实例层，保存面向当前 C 验证义务的辅助引理；策略证明不依赖这一层。

旧 Record 版说明保存在 `reports/typeinfer_rc-20261026155929/record-interface-design-before.md`。下文 Module Type 设计仍适用。list-based missing 重构的初始 run `typeinfer_rc-20261027100754` 因库 seed 的三处禁用 tactic 阻塞，记录和部分迁移证明均保留。续接 run `typeinfer_rc-20261027114106` 只等价改写这三处证明体，随后 28 组全部接纳、完整 parent 编译通过；但最终发布遇到 Windows 目录重命名错误，重试报告 publication conflict。完整证明目前在 proving_merged 候选中，尚未写回主 manual，也未完成 final-check，详见第 13 节。

## 1. 模块结构与使用方式

`RCMap` 仍是通用参考账本的实现模块，保存单层节点、引用账目以及参考操作。围绕它新增的模块接口是：

| 名称 | 职责 |
|---|---|
| `RC_PAYLOAD_SIG` | 节点类型及 owning children 的签名 |
| `RCMAP_SIG (P : RC_PAYLOAD_SIG)` | 在 P 上定义 RC 状态、操作、程序和规律 |
| `MakeRCMap (P : RC_PAYLOAD_SIG) <: RCMAP_SIG P` | 用参考账本提供具体实现，证明所有签名要求 |
| `RCMapFacts (P : RC_PAYLOAD_SIG) (I : RCMAP_SIG P)` | 仅根据接口规律证明通用性质 |
| `TypePayload`、`TypeRCMap` | type case 的具体 payload 模块和 RC 模块 |
| `VariadicPayloadDemo`、`VariadicRCMapDemo` | 任意长度子列表的第二个具体模块 |

实际 type 实例化为：

```coq
Module TypePayload <: RC_PAYLOAD_SIG.
  Definition node := TypeNode.
  Definition children := node_children.
End TypePayload.

Module TypeRCMap := MakeRCMap TypePayload.
Module TypeRCMapFacts := RCMapFacts TypePayload TypeRCMap.
Definition RcState := TypeRCMap.state.
```

以后更换复用对象但沿用同一账本算法，提供另一个 payload 模块即可。若需要不同状态表示或操作实现，则实现 `RCMAP_SIG P` 的全部要求，再用 `RCMapFacts P YourRCMap` 获得通用引理。

模块参数不是类型类实例搜索：依赖显式出现在 functor 的模块参数中，调用为 `TypeRCMap.retain M p`，不再是 `rcmap_retain TypeRCMap M p`。

## 2. Parameter、Definition、Lemma 分别在做什么？

在 `Module Type` 内：

- `Parameter` 声明具体实现必须提供的成员，可以是类型、函数或命题的证明。
- `Definition` 不仅给成员的类型，还固定它的定义；实现不能随意换成另一个无关观察器。

在具体实现模块中：

- 类型和操作用 `Definition` 给出。
- 性质用 `Lemma ... Proof ... Qed.` 证明。
- `<:` 检查实现满足签名，同时保留具体定义的透明性，方便当前 case 归约账本表示。

例如：

```coq
Module Type RC_PAYLOAD_SIG.
  Parameter node : Type.
  Parameter children : node -> list addr.
End RC_PAYLOAD_SIG.
```

它没有提供一个可供全局直接使用的“未证明节点实现”。只有给出具体模块后，才得到该模块的节点类型和操作。同样，`Parameter retain_view : ...` 是实现义务，`MakeRCMap` 必须交付该证明。

这与签名外的 `Parameter impossible : False.` 或 `Declare Module M : SOME_SIG.` 不同；后两者可以引入没有实现支撑的全局假设，当前检查器仍拒绝。

`TypeNode` 和参考账本内部仍可以使用普通 Record 来描述数据。这与“接口是否走 TypeClass/Module Type 路线”是两件事；被替换的是接口记录，不是禁止全部 Record 数据结构。

## 3. MonadErr 为什么仍在底层？

只有一种程序类型：

```coq
Notation RCProgram := (MonadErr.M unit).
```

程序正文统一使用 `ret`、`<-`、`;;`。本轮增加了真正进入源码的语义包装：

```coq
Definition rc_returns {A : Type} (c : RCProgram A) (a : A) : Prop :=
  MonadErr.nrm c tt a tt.

Definition rc_errors {A : Type} (c : RCProgram A) : Prop :=
  MonadErr.err c tt.
```

Sig 使用这些包装，不直接写 `MonadErr.nrm/err`。底层依赖和部分实现证明仍使用这些投影；这是隐藏实现名字，不是删除错误语义，也不是切换到第二种 monad。

`unit` 是隐式状态类型，唯一值为 `tt`。真实 RC 账本 M 仍显式传入、通过返回值传出；`rc_returns (TypeRCMap.release_program M p) M'` 表示程序可以正常返回新账本 M'。

需要区分：

- `ret (1,M,s)` / `ret (2,M,s)`：C 算法正常返回失败码，仍是正常结果。
- `rc_errors c`：当前模型中容量 assert 可能失败。
- `~ rc_errors c`：排除错误行为，不保证终止或存在正常返回。

`assert P` 不可直接改成 `testPure P`：P 不成立时，前者报错，后者只是排除该分支。这样替换会隐藏不安全行为，而不是证明它安全。

底层定义见 [MonadErrBasic.v](../../../MonadLib/MonadErr/MonadErrBasic.v)。`Monad.bind` 是类型类接口分派到所选 monad 的 bind；证明里同时出现它和 `MonadErr.bind` 不表示混用了两种程序语义。

## 4. RC_PAYLOAD_SIG 的全部 2 项

| 成员 | 类型 | 含义与设计原因 |
|---|---|---|
| `node` | `Type` | 一个节点的一层逻辑内容；不把 TypeTree 或表达式写死在通用库里 |
| `children` | `node -> list addr` | 节点拥有的子引用地址列表，供计数和删除后递归释放使用 |

children 只列 owning 引用，不能把借用指针算进去。使用 list 而非 set，因为 `[q;q]` 是两条拥有的引用，需要计数和释放两次。

type 的 Arrow/Apply 节点里存两个子地址，而不是直接嵌套两棵树；数学树由 `decode_type` 解释。第二个 payload 模块使用 `(Z * list addr)`，以第二部分为 children，展示不是只能支持二叉类型节点。

## 5. 参考账本的含义

签名的 view 指向固定参考账本 `RCMap.t P.node`：

| 数据 | 含义 |
|---|---|
| `nodes` | 地址到单层 payload 的部分映射；None 表示不在活节点图中 |
| `roots` | 图外部持有的 owning 引用数，包含临时引用 |
| `counts` | 物理 refcnt 字段应具有的值 |
| `reserved` | roots 中尚未交给外部容器的临时引用预算 |

有效状态满足：

```text
counts(p) = roots(p) + 指向 p 的图内 owning 边数
0 <= reserved(p) <= roots(p)
外部容器可使用的预算 = roots(p) - reserved(p)
```

reserved 已计入 roots，不是第二个物理计数。它用于区分递归调用暂时 retain 的引用和 solution 槽位拥有的引用，避免临时 retain 被错误用来支持额外的容器槽位。

valid 还要求活节点有限、边闭合、无环、根数非负、活地址非零、活计数在正数至 2147483647 内、死节点账目归零。有限性及无环 rank 是 Prop 中的见证，不要求运行时保存 Live_keys。

## 6. RCMAP_SIG 的 16 项待实现成员

下面 I 表示实现模块，S 表示其 state。所有名字均与当前源码一致。

### 6.1 状态与解释：2 项

| 成员 | 类型 | 意义与理由 |
|---|---|---|
| `state` | `Type` | 具体 RC 实现的状态类型，可以不同于参考账本 |
| `view` | `state -> RCMap.t P.node` | 将实现状态解释成统一账本，便于复用不变量和操作定理 |

view 是纯数学函数，不是 C 内存遍历程序，也不产生 points-to 权限。

不要求 view 单射，因此不同缓存状态可表示同一账本；也不要求覆盖所有参考账本。但后面的正常结果规律要求：从某个已有实现状态出发，参考程序的每个正常输出都必须有对应实现输出。

当前规律对全部 state 值成立，没有额外的“表示有效”前提。需要缓存不变量的实现可以把约束放入状态类型；不能不加证明就声称任意缓存表示均可接入。

### 6.2 纯账本变换：4 项

| 成员 | 类型 | 效果 |
|---|---|---|
| `retain` | `state -> addr -> state` | 非空地址的 roots/counts/reserved 同时加一；空地址不变 |
| `publish` | `state -> addr -> state` | reserved 减一，将临时引用交给容器；counts 不变 |
| `delete` | `state -> addr -> P.node -> state` | 删除父节点，将每条子边转成孩子的临时根；孩子 counts 暂时不变 |
| `decrement` | `state -> addr -> state` | roots/counts/reserved 同时减一，节点和子边不变 |

这些函数不检查调用前提、不操作 C 堆。安全调用 publish 需要 reserved 可消耗；delete 需对应真实 payload 并用于最后一次释放；decrement 需有临时引用且计数大于一。

保留纯操作是为了描述 C 的中间状态，例如父节点已删除、孩子尚未释放。它们与后面的完整 monad 程序是不同层次，不是两种 monad。将来可以缩小公开 API，但当前证明依赖这些中间状态，不能直接删掉。

### 6.3 纯操作的 view 规律：4 项

| 成员 | 必须实现的性质 | 作用 |
|---|---|---|
| `retain_view` | `view (retain M p) = RCMap.retain (view M) p` | retain 不得漏增引用或更改 payload |
| `publish_view` | `view (publish M p) = RCMap.publish (view M) p` | 只转交预算，不制造额外引用 |
| `delete_view` | `view (delete M p n) = RCMap.delete P.children (view M) p n` | 删除及转交子引用遵守参考账目，包括重复边 |
| `decrement_view` | `view (decrement M p) = RCMap.decrement (view M) p` | 三项计数同步递减 |

这些是实现必须提供的证明。等式规定操作的含义，不意味着对任意非法输入操作后也保持 valid。

### 6.4 monad 程序：2 项

| 成员 | 类型 | 含义 |
|---|---|---|
| `retain_program` | `state -> addr -> RCProgram state` | 容量检查通过后返回 retain 后账本，否则产生错误行为 |
| `release_program` | `state -> addr -> RCProgram state` | 从待释放地址开始递归释放，返回最终账本 |

参考 release 将 `(jobs,M)` 作为递归参数，通过 Rec 定义关系式不动点：空工作表返回 M；空地址跳过；计数一时删除父节点，将 children 放到工作表前；否则递减计数。

当前 release 没有主动产生错误的构造，但仍使用同一个 RCProgram。它在参考模型中跳过不存在地址，不意味着 C 可以安全 free 任意非法指针；内存安全仍依赖有效性和资源前提。

这是关系式程序，不承诺可直接提取成可执行 map 算法，也不要求提取有限性见证。

### 6.5 正常结果与错误规律：4 项

| 成员 | 性质 | 目的 |
|---|---|---|
| `retain_nrm` | 实现 retain 的正常输出经 view 解释后，恰好是参考 retain 的正常输出 | 不伪造、不遗漏结果 |
| `retain_err` | 实现 retain 与参考 retain 的 rc_errors 等价 | 不忽略容量错误，也不额外报错 |
| `release_nrm` | 实现 release 的正常输出经 view 解释后，恰好是参考 release 的正常输出 | 递归回收的可观察结果一致 |
| `release_err` | 实现 release 与参考 release 的 rc_errors 等价 | 不把释放行为替换成错误行为 |

例如 retain_nrm 的当前形式为：

```coq
Parameter retain_nrm : forall M p V,
  (exists M', rc_returns (retain_program M p) M' /\ view M' = V) <->
  rc_returns (RCMap.retain_program (view M) p) V.
```

量化参考输出 V，再存在实现输出 M'，是为了允许不同表示和非单射 view。不能直接要求 M'=V，因为二者类型可以不同。

使用 iff 是较强的设计选择。只有单向“实现结果都合法”时，永不正常返回的实现可以空泛满足条件；反向方向要求覆盖参考正常结果。但若参考程序没有正常结果，这仍不是额外的终止保证。

正常结果关系不能控制错误分量，因此还要约束 rc_errors。一个保留全部正常结果却额外报错的程序，会被错误规律排除。

## 7. RCMAP_SIG 的 6 项固定派生定义

这六项在签名中是 Definition，而不是 Parameter：

| 成员 | 定义来源 |
|---|---|
| `nodes M` | `RCMap.nodes (view M)` |
| `roots M` | `RCMap.roots (view M)` |
| `counts M` | `RCMap.counts (view M)` |
| `reserved M` | `RCMap.reserved (view M)` |
| `valid M` | `RCMap.valid P.children (view M)` |
| `preserves B M` | `RCMap.preserves (view B) (view M)` |

preserves 表示原有节点内容保持、原有 roots 不减少；一般 release 不自动满足它。

这些观察器已由 view 唯一决定。若允许各实例独立填写，还需增加它们与 view 一致的六组证明。固定 Definition 减少了重复配置，也让 RCMapFacts 可直接展开这些定义、再用 view 规律证明通用性质。

MakeRCMap 中写出对应 Definition，Rocq 的模块匹配检查它们符合签名中固定的定义。

## 8. MakeRCMap 如何履行签名？

默认实现选择参考账本作为 state，view 为恒等函数，四个纯操作及两个程序复用 kernel。四条 view 等式、两条正常结果等价和两条错误等价均在模块中证明。

`RCMapFacts` 的 retain_valid、retain_preserves、publish_valid、retain_available 只依赖接口规律，不必知道实现 state 的具体表示。这体现了模块接口的实际用途。

typeinfer 的整份 C 证明仍针对具体 TypeRCMap，部分表示层证明通过 `type_rcmap_reduce` 展开默认实现。不能因此宣称“任意实现 RCMAP_SIG 的模块都自动得到同一份 typeinfer C 验证”；那需要进一步参数化堆表示和整份证明。

## 9. 与 store_type / store_solution / store_world 的关系

Sig 不包含堆权限。当前 type case 在模块之外连接内存：

- `store_type M p tr : Prop`：纯解码关系，不拥有节点，也不是可独立释放的 owning token。
- `store_node M p n`：拥有一个节点的 refcnt 和 payload；物理 refcnt 等于 TypeRCMap.counts M p。
- `store_world M`：每个活节点的字段恰好一份，共享子节点也不重复拥有。
- `store_solution M res s`：拥有 solution 数组槽位，用 M 解释地址并核对引用预算；M 中仍只存 type 节点。

map 查询只能为拆分 store_world 提供纯依据，不能凭查询结果凭空产生 points-to 权限。指针槽位的权限和目标节点的权限也应区分。

例：父节点 p 有三条边 `[q;q;q]`，q 另被一个外部槽位拥有。q 初始 roots=1、reserved=0、counts=4。删除最后引用的 p 后，q 为 roots=4、reserved=3、counts=4；释放三次临时引用后恢复为 roots=1、reserved=0、counts=1。q 的物理节点始终只有一份。

## 10. 通用性边界和取舍

- 这是“有固定参考模型的实现接口”，不是任意 RC 政策的最小公理体系；view 的目标仍是 RCMap.t。
- payload、状态表示和符合规律的实现可变；DAG、32 位正计数上界、roots/reserved 政策仍固定在 kernel。
- 仅为换 payload 时，MakeRCMap 已够用；state/view 层为更换实现表示预留空间。
- 四个纯操作公开是为了当前 C 中间状态证明，并非任何 RC 库都必须如此设计。
- 不支持带环垃圾回收；也不提供自动分配节点、跨 map owning 边计账或独立线性句柄协议。
- 若将表达式和类型放进同一个和类型 payload，可以描述混合节点图，但仍需另证内存解释；若分为两个 map，跨 map 引用不会自动计入 incoming。
- 多个独立容器不能各自重复消费同一 roots-reserved 上界，必须核对合计用量或另建线性凭证。
- 变长模块 demo 证明重复边释放，不代表表达式匹配 C 程序已经验证。

## 11. 检查器如何支持 Module Type，同时保留安全边界？

以前词法检查无条件拒绝 Parameter。2026-10-26 的 Module Type 迁移在
[`proof_manual_utils.py`](../../../../.agents/scripts/vc-proving/proof_manual_utils.py)
中增加作用域识别：

1. 区分交互式 Module Type、普通 Module、Section；正确匹配 End。
2. 仅在最内层模块作用域为 Module Type 且不在证明体内时，允许 Parameter/Parameters。
3. Module/Module Type 的别名赋值不打开新作用域；注释和字符串不能伪造作用域。
4. 签名结束后恢复拒绝 Parameter；嵌套普通实现模块也不继承签名豁免。
5. Axiom/Conjecture、回滚控制、关闭类型检查仍拒绝。
6. Declare Module 没有实际实现，会被拒绝，避免凭声明直接取得签名中的要求。
7. 作用域匹配错误报错；最终语法、模块匹配和证明有效性仍由 Rocq 编译检查。

这里只允许明确需要的 Parameter 字段，不是把签名内的所有假设形式全部放行。

回归测试见 [test_module_signature_safety.py](../../../../.agents/scripts/tests/test_module_signature_safety.py)，包括合法签名、嵌套 Section/Module、别名、修饰符、注释/字符串以及负例。Module Type 迁移当时的定向与 staging/timeout 测试共 49 项通过；这不是本次 missing 迁移重新运行的测试结果。当时完整 Python suite 在收集时因已有的 test_script_regressions.py 导入缺失 witness_reuse 而失败；未为本任务修补无关旧测试。

Module Type 迁移的正式验证 run 为 `typeinfer_rc-20261026155929`，已完成并返回 `{"status":"passed","phase":"done","errors":[]}`。以下统计仅对应该轮，早于三层抽取和 missing/strategies 重构：

- 112 条顶层 VC、119 条 split，分为 26 组；全部通过接纳、完整 parent 编译、写回复查及独立 symexec 重生成终检。
- 最终 manual 有 231 个 Qed，lib 与 manual 均无 Admitted；26 个证明组未新增 helper，也未改写 annotation seed。
- C 文件（含 spec）和原 typeinfer 的 type_infer_lib.v、sound_pv.v、sol_prop.v 的 SHA-256 与本轮开始时一致；数学正确性没有改变。
- 注意：生成的 typeinfer_rc_proof_auto.v 仍有原有的 185 个 Admitted。本轮通过的是现有验证流程下的 manual/lib 及完整编译检查，不能据此宣称整个 case 无假设。

逐组说明、编译记录和终检状态保存在仓库 `reports/typeinfer_rc-20261026155929/`，历史源码与合并候选保存在 `verification_runs/typeinfer_rc-20261026155929/`。本轮未执行 commit 或 push。

## 12. 字段级 missing 的统一表示（2026-10-27 重构）

这一层属于 [typeinfer_rc.v](./typeinfer_rc.v) 的具体堆解释，不属于通用 RCMap 的计数语义。

`TypeFieldKey` 由节点地址与 `TypeFieldSlot` 组成。槽位为 `RefCount`、`Tag`、`Payload0`、`Payload1`；不是把 union 的不同成员名字当作不同资源。`Payload0` 根据当前节点 tag 解释为 Atom/Var 的整数 name，或 Arrow/Apply 的第一个子地址；叶子节点没有可读的第二个 payload 字段。

`store_world_missing M L` 仍遍历 M 的同一组活节点，但每个节点的字段通过 list membership 决定是否保留：key 在 L 中时，该字段贡献 emp；不在 L 中时，保留它对应的 points-to。list 记录的是已拆出字段的标识，不包含权限或字段值，也不是运行时数据结构。

因此只需一个 predicate 表达任意组合，例如 `[(p, RefCount)]` 缺一个计数字段，`[(p, Payload0); (p, Payload1)]` 缺一个复合节点的两条子地址字段。多个节点的字段也放进同一个 list，不增加单节点/双节点专用定义。

核心规律的形状为：

```text
missing M []  等价于  store_world M

M[p] = n 且 (p,s) 不在 L 中：
  missing M L
    |-- field(M,p,n,s) * missing M ((p,s)::L)

  field(M,p,n,s) * missing M ((p,s)::L)
    |-- missing M L
```

这些规律需要实际证明，不采用 GlobalStrings_missing 的 Parameter/Axiom 声明方式。字段解释依赖 M 中的实际节点；仅有地址或纯 store_type 不会产生权限。list 的排列不改变缺失集合，重复 key 也不产生第二份权限；能够拆出新权限的 split 必须满足不在 list 中的前提。别名节点因此不能被重复拆出。

策略是这些证明规律的使用方式，不是额外公理。依赖方向为：通用 RCMap → type 实例及 missing 引理 → 策略 goal/proof；主 VC lib 同样依赖 type 实例，并导入 strategy_goal_check 检查策略证明确实履行生成的接口。策略证明不反向依赖主 VC lib。

当前 [typeinfer_rc.strategies](../../../../QCP_examples/Applications_human/typeinfer_rc/typeinfer_rc.strategies) 的基础规则为：

- 0/1：完整 world 与空 missing list 相互衔接。
- 2/3：拆出或归还一个字段；freshness 是需要证明的条件，不是仅检查文本中没有出现某个 key。
- 4：同一个 M、同一个地址的 node_at 查询有唯一结果。missing list 不再携带旧 frame 中的节点参数，这条纯规则帮助匹配已有节点信息，不产生堆权限。
- 5/6：将通用字段规则特化到 C 的 tag points-to，直接用于现有读 tag 的桥。拆出规则从空 missing list 起步，避免对已经拆出的字段再次尝试；归还仍要求对应 key 的 freshness。

旧 without 形状仅暂存在 VC lib 内部的 TypeinferRCFrameCompat 模块，作为旧证明到 missing 的等价桥；C/header 和实例层不再把它们作为另一套存储接口。单节点桥要求节点确实属于 M；双节点桥还要求地址不同。地址相同的分支只拆一份字段，不能使用双节点桥。

这 7 条策略证明及 strategy_goal_check 已通过 controller 的实际编译。符号执行生成的 atype_unify / atype_unify1 对应 tag 桥中出现了 field_fresh(key,[]) 的纯义务，说明拆出/归还规则实际参与推导，并非仅有未使用的策略文件。114 个 manual 顶层义务、127 个 split 已全部由 28 组证明并接纳，完整合并 parent 编译通过；发布恢复修复后，正式写回和独立终检也已通过（见下节）。生成 auto 文件现有 193 个 Admitted 占位（重构前为 185），不在 manual 分组计划内，必须单独披露，不能宣称整个 case 已无假设验证。

按用户最新要求，本轮保留现有 which-implies 结构。利用 strategies 精简这些 annotation 是后续独立工作，不和当前证明迁移混做。

## 13. 本轮验证结果与发布恢复

续接 run：`typeinfer_rc-20261027114106`。

- annotation 三项检查、接纳、独立 VC 检查和 28 组接纳全部通过；证明组没有新增 helper。
- `vc-proving-verify` 完整编译当前 lib、goal、auto、manual、goal-check，返回 passed，group_errors 为空；parent 编译用时 460.343 秒。
- 合并 manual 有 241 个 Qed、0 个 Admitted；合并 lib 有 148 个 Qed、0 个 Admitted。策略 proof 有 7 个 Qed；通用 RCMap 与实例源码均无 Admitted。
- 与重构前对比：C 的执行函数体、移入 header 的 enum/struct、6 处含 unify_rel/sol_correct_iter 的完整数学契约均未改变（忽略空白/注释）；原数学库三文件与 .agents 两份既有改动文件的 SHA-256 保持原值。本轮未改 .agents、build 配置或 release 接口，未 commit/push。

完整候选：

- [typeinfer_rc_proof_manual.v](../../../../verification_runs/typeinfer_rc-20261027114106/typeinfer_rc-vc-proving-r1/proving_merged/typeinfer_rc_proof_manual.v)
- [typeinfer_rc_lib.v](../../../../verification_runs/typeinfer_rc-20261027114106/typeinfer_rc-vc-proving-r1/proving_merged/typeinfer_rc_lib.v)
- [controller 状态](../../../../reports/typeinfer_rc-20261027114106/controller_state.json)

2026-10-27 的 final-apply 在候选重查之后、修改主文件之前失败：把临时 transaction 目录重命名为 final-check/backup 时出现 WinError 5（拒绝访问）。只读检查确认 backup 不存在，主 manual 仍是生成的 114 个 Admitted，而不是上面的已证明候选。按 controller 给出的动作重试后，返回 `publication-conflict: final publication backup is missing`；当前 step 无 next_actions、无 running owner。

以上为首次发布失败时的历史记录。当时没有手动编辑 controller 状态、伪造备份或强行覆盖主文件。

随后经用户授权，仅修复 `.agents` 的发布恢复逻辑：未建立备份的已回滚事务可以幂等重试；已发布但缺少备份、外部修改和异常路径仍阻止覆盖。备份目录建立对 Windows 访问/共享错误采用有限重试，并且只恢复本次实际建立的事务。对应新增回归测试与既有定向测试共 69 项通过；全量 Python 测试仍被既有 `witness_reuse` 模块缺失阻断。

原 run 经正常 `final-apply` 重新编译并发布，再由 `final-check` 独立符号执行、检查当前义务和编译当前源码，于 2026-10-27 05:03:22 UTC 返回 `{"status":"passed","phase":"done","errors":[]}`。正式 manual 为 241 个 Qed、0 个 Admitted，lib 为 148 个 Qed、0 个 Admitted，策略 proof 为 7 个 Qed、0 个 Admitted。C/header、策略、RCMap、type 实例和原 typeinfer 数学库的哈希均未改变；which-implies 精简仍留待后续。

构建登记：`Rocq/Makefile` 的 `SL_FILES` 包含 `RCMap.v`，`APPLICATION_Lib_FILES` 包含实例和 VC lib，`APPLICATION_STRATEGY_FILE_NAME` 包含 `typeinfer_rc/typeinfer_rc`，由现有规则展开三个策略文件并生成依赖。Dune 的 qualified 子目录自动收录这些源码，无需新增排除项。上述 run 的完整日志和候选保留在本地，不作为构建依赖。

发布前合并远端 `308f03cd1`，保留其 MiniGMP 布局与检查器更新，并补充 Linux/Windows 的 RC 策略生成入口及 Make 源码清单回归断言。合并未改变上述 run 依赖清单中的 165 份 Rocq 源码，也未改变 C/header/strategies。使用绝对路径 `DUNE_EXE` 运行 `scripts/tests` 和 `.agents/scripts/tests`（排除已有缺失导入的 `test_script_regressions.py`）共 125 项通过，包括原生 Dune/Make fixture；这不等于重新执行整个仓库的形式验证。
