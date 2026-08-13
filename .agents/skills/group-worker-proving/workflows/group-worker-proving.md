# Group 证明流程

本流程由一个 group-worker 执行。它只解决 controller 在当前 claim/handoff 中分配给本组的 witnesses，不修改 main root 正式文件，不与 sibling group 建立依赖，不负责任何 parent 阶段。

## 一、开始与读取顺序

main agent 已经执行 controller 给出的 `claim_invocation`。首次领取或同 owner 追加修复时，消息都应包含 `Role`、`Owner`、`CWD` 和逐字保留的 `Claim message`。先确认 role 是当前 group-worker、owner 与 claim message 一致，并始终在给出的 `CWD` 工作；不要自行运行或重建 claim。若四段缺失、互相矛盾或指向的当前交接不存在，停止扩展读取并按已绑定的报告合同指出缺失项，不从 run state 或其他角色文档重建上下文。

开始 formal 工作前按以下顺序完整读取：

1. `group-worker-proving/SKILL.md`、本流程、命令规则和禁用 lemma 原则。
2. `Claim message` 指定的当前 `group_worker_input.md`。
3. `SKILL.md` 按目标导航的证明知识文档。
4. 阅读 round 开始时冻结的 `public_helper_snapshot.txt`。
5. 若存在 `proof_reuse.md`，按其中顺序读取 helper、split goal、top-level VC 的复用提示。

当前 `group_worker_input.md` 是本 worker 的唯一 scope 来源。它应给出本组 owner/group 身份、固定工作与报告路径、assigned witnesses、每个 witness 的 `proof_mode` 与适用的 split goals、copied manual、可选 `group_worker_lib`、helper suffix、public snapshot/reuse 提示以及可执行命令。只使用其中的 exact path、name、assignment 和 argv，不从 C stem、目录名或其他文件推测。

不读 orchestrator 或其他角色 skill，不依赖 parent transcript，不读 `controller_state.json`、`group_workers_manifest.json` 或 sibling 输出来补全交接。如执行本组任务所必需的交接字段缺失或互相矛盾，按现有 blocker 合同精确报告交接位置；不向 scope 外搜索或自行修改 plan。

controller 返回 `append-group-worker` 时，必须由相同 owner 在相同 group directory 继续。先完整读取追加到 `group_worker_input.md` 的 category、message、required repair 和本次开放的写入边界：formal repair 只修正原 copied files；report-only repair 只修正报告和可选说明，不得再动 formal files。

## 二、写入边界

允许修改：

- 本组 copied manual 中被分配的 proof spans；
- 仅在交接明确提供时修改本组 `group_worker_lib`；
- 交接明确给出的 debug script；
- `group_worker_report.json`；
- 可选 `group_worker_output.md`。

只读：

- statement、manual declaration order 和未分配 proof spans；
- main root `formal_case_lib`；
- generated files；
- `public_helper_snapshot.txt`；
- `proof_reuse.md` 引用的 previous source；
- sibling group 的全部文件。

不得修改 main root 正式 manual/lib、shared 或异名 lib、generated files、durable public pool、plan/manifest/state 或 sibling 文件。若交接中 `group_worker_lib` 为 missing/未提供，不得创建它，不得新增 helper/import，也不得转而修改任何共享 lib。

group directory 最终只能有 copied manual 和交接已提供的可选 `group_worker_lib`。报告和 debug/build 文件分别位于交接指定的 report path 与 `_coq_builds`；不自行创建其他文件或目录。

controller 按 Rocq token 检查语义写入边界。注释、空白、CRLF/LF、行尾空白和 EOF 换行差异不视为 proof token 修改；statement、未分配 proof 和 `LLM_pre_process` split block 的 token 仍受严格保护。

## 三、按 `proof_mode` 完成 manual

以交接列出的 assigned top-level witnesses 为闭合 scope。对每个 witness 只执行其 accepted `proof_mode`；即使其他 declaration 看似相同，也不证明、修改或依赖未分配 witness。交接的 mode/split mapping 若与 copied manual 矛盾，不自行改 mode 或 plan，而是按 blocker 合同精确报告矛盾位置。

### `aggressive_pre_process` 模式

只编辑：

- 当前 top-level VC proof span；
- 交接列出的全部 split-goal proof spans。

步骤：

1. 先逐个完成全部 split goals，每个都以 `LLM_pre_process ltac:(...)` 开头。
2. 在 top-level VC 中使用 `aggressive_pre_process`。
3. 对 `aggressive_pre_process` 产生的每个分支，只使用 `Goal_apply <对应 split-goal lemma>.` 完成，不写其他 tactic。
4. 每个 split lemma 都要应用到对应分支；不得用 `apply`、`eapply`、`exact`、`refine`、局部别名或其他方式代替 `Goal_apply`。

这是 group-worker 必须遵循的证明原则。controller 不检查 top-level proof 是否逐字使用 `Goal_apply`，只检查所选 `proof_mode`、split goal 完整性、写入边界和 Rocq 结果。

### `LLM_pre_process` 模式

只编辑 top-level VC proof span，并按当前目标选择合适的参数执行 `LLM_pre_process ltac:(...)`。对应 split-goal block 必须继续保持 `Proof. Abort.` 的 Rocq token；只允许注释、空白和换行差异。

### 两种模式共同的骨架与禁用 tactic

`aggressive_pre_process` 只出现在有 split goals 的 top-level VC，其后只跟 `Goal_apply`；其余全部 proof（split goals，以及 `LLM_pre_process` route 的 top-level VC）一律以 `LLM_pre_process ltac:(...)` 开头并显式写出 closer。

proof 文本中禁止出现 `entailer!` 和别名 `pre_process`，与 forbidden lemma 同一扫描，命中即 `forbidden-lemma` 失败；`LLM_pre_process` 和 `Goal_apply` 内部的调用不受影响。改写方式见[完整分离逻辑证明方法](../docs/separation-logic-whole-proof-tactics.md)。

## 四、Helper、import 与 `group_worker_lib`

仅在交接提供 `group_worker_lib` 时，才允许在其中新增已证明的 `Lemma`、`Theorem`、`Fact`、`Remark` 和必要的 Rocq 官方 import。helper 必须在本 lib 中完整证明，不得放入 copied manual。

命名规则：

- 每个全新、改写或重命名的 helper 必须以 `helper_namespace.suffix` 结尾。
- plan 中的 helper 使用交接给出的 exact name。
- 只有与冻结 snapshot 或 accepted helper reuse row 的 declaration/proof token 一致时，才能保留历史或其他 group suffix。
- 对已有 helper 作实质修改时，必须视为当前 group 的新 helper 并使用当前 suffix。

只可添加证明确实必需且已被 accepted dependency snapshot覆盖的 project import，或 Rocq installed standard-library import。禁止修改 seed declaration，禁止加入 generated/current/sibling import，禁止编辑 durable pool，也禁止把 snapshot 当成 `.v` library import。快照外 project import 不能在本组动态准备；精确记录需求并按 controller 反馈返回 annotation。worker 不观察依赖图、不调用 Dune、Make 或 `coqdep`，也不自己扩大 build target。

`public_helper_snapshot.txt` 是 round-start 只读目录。可以把其中 token 一致的已证 helper 完整复制进 `group_worker_lib`；本 round 其他 group 后来晋升到 `public_helper_lemma_lib.v` 的内容对本组不可见。

planned helper 的 `visibility` 为 `local` 时只属于本组候选；为 `public` 时，也只有本组通过 controller validation 后，controller 才会把它和必要的本地 helper 依赖闭包追加到 durable pool，供未来 round 使用。worker 不向 sibling 发布文件，不将 public helper 当成当轮跨组依赖，也不等待 pool 更新。

后续 merge 若遇到同名但 token 不一致的合法 helper，由 controller 只在 merged candidate 中确定 canonical block、改名其他 variant 并改写本组引用；worker 不预判合并结果，不读取或修改其他 group 名称。

## 五、使用复用提示

`proof_reuse.md` 只在 controller 绑定上一封存 proving source 时存在。读取顺序固定为：

1. 全部 helper rows；
2. 全部 aggressive split rows；
3. 全部 `LLM_pre_process` top-level rows。

aggressive top-level VC 没有独立复用行；它只按当前 split goals 和上述 `Goal_apply` 原则完成。

每个非 `from scratch` 的行范围应覆盖完整 declaration：

- helper `direct copy` 与 proof `direct copy` 只来自 previous accepted group。
- proof direct 还已通过 generated-goal 语义指纹比较；只改 generated declaration 名称仍可 direct。
- `partial proof-idea reuse` 只提供思路。worker 必须自行证明 `P |-- P'`、`Q' |-- Q` adapter 或共同 frame 转换。
- failed 或 blocked 来源中未 accepted 的 proof 最多 partial，其中 helper 必须从头证明。

所有 previous 文件只读。复用提示不能改变本组 assignment、`proof_mode`、命令或 validation 要求。

## 六、证明循环

1. 先读当前目标和已有 helper。
2. 需要时写交接指定的 debug script，并原样运行 `coq-debug`。
3. 优先使用 `group-development` 获取较快反馈；它允许本组可编辑 proof span 暂时 `Abort.`。
4. 修正 assigned proof，并仅在存在且需要时修正 `group_worker_lib`。
5. 需要时运行 exact `group-check`；它要求本组证明和路线完整。
6. 交付前检查 assignment/mode、helper suffix/import、写入边界和禁用原则；不得留下 `Admitted.`、额外 `Axiom` 或禁用 lemma，annotation gap 的终态副本也不得用这些方式伪造进度。
7. 写最终报告；`annotation-gap` 终态必须同时写 `group_worker_output.md`，其他终态按需写该说明。然后停止修改 report/manual/lib。
8. 把结果交回 main agent。main agent 原样调用 claim/handoff 中绑定的 `finalize-delivery`，controller 封存 report、manual 和适用时的 lib，再执行唯一强制 group validation。

development 和 exact 都是可选的提前检查，不是 owner 报告的前置凭据。即使 exact 通过，最终接纳仍由 finalize 后对封存 bytes 的 controller validation 决定。worker 不自行运行 claim/finalize，不调用 controller `step`，不尝试 merge、parent verify 或 annotation retry。

## 七、修正与阻塞

### 本组内可修问题

以下情况应在本地继续修正，不写 `blocked`：

- tactic 失败；
- 缺少可选复用提示；
- 需要新增带 suffix 的 helper；
- 需要多轮 debug；
- controller 返回可修的 structure、route、proof-completeness 或 safety 问题。

可修问题会通过 `append-group-worker` 追加给相同 worker。按交接开放的精确边界修正 copied manual 或适用时的 `group_worker_lib`，重写终态报告，停止写入后再交付。

### Annotation/spec 缺口

只有具体 proof state 与合法 helper 路径共同表明以下事实时，才诊断 annotation/spec 缺口：

- 当前 assigned witness 的 hypotheses 确实缺少完成目标所需的语义 premise；
- 该 premise 不能由现有 helper、frozen/reuse helper、常规 proof transformation 或一个合法的当前 suffix helper 在现有前提下证明；
- 修复必须改变 group-worker 写入边界之外的数学规范、function contract、loop invariant、assertion 或调用实例。

一旦诊断成立：

1. 把它视为本 group 当前 delivery 的终态，不再在 copied manual 或 `group_worker_lib` 中追加试图代替 annotation 的证明修正，更不得修改 statement、main root 或未分配 proof。
2. 保留已有合法副本，在 `group_worker_output.md` 中写清交接给出的 group id、每个受影响 assigned witness、top-level/split 位置、具体缺失 premise、已尝试 helper/route 以及必须修改的 annotation/spec 边界。
3. 写入 `status: blocked` 的完整机器报告，其 `blocker.failure_class` 必须精确为 `annotation-gap`；具体缺少 annotation premise 时使用 `kind: missing-annotation-premise`。`location` 必须按 witness 列出受影响 declaration/proof state，`message` 必须给出可诊断的缺失事实，`repair_boundary` 必须指向实际需要修改的 annotation/spec 边界。
4. 停止所有 formal/report 写入并把结果交回 main agent，使当前 delivery 可按正常 `finalize-delivery` 路径封存。

这个终态只描述本 group。worker 不读取或查询 sibling 状态，不要求取消尚未领取的 group，不等待其他 group 结束，不创建 annotation feedback/retry，也不尝试推进 merge 或 parent verify。其他 group 和后续轮次由 controller/main agent 处理。

### 其他 blocker 与报告原地修复

对证明类 blocker，只有具体 proof state/helper 明确显示必要 premise 不可推出时才能阻塞，不得把普通 tactic 搜索失败当成终态。工具/资源、交接、版本或其他 blocker 继续使用现有 `failure_class`/`kind` 语义与修复边界；交接命令所代表的 exact 工具完全不可运行时可按既有 tool/resource blocker 报告。这些情况不得为了获得本轮汇总而误标为 `annotation-gap`。版本失效使用现有 `stale` 分类；上下文压缩使用现有 `compact-error` 分类。

若 finalize 只返回最终报告字段合同错误，delivery 仍是同一 claimed attempt，且由同 owner 原地修复。修正范围只开放 `group_worker_report.json` 和可选 `group_worker_output.md`；controller 已封存的 copied manual 和适用时的 `group_worker_lib` 必须保持 byte/token 不变。修正报告后再停止写入并交回 main agent 重跑原 `finalize-delivery`。formal 漂移会形成不可复用的 `invalid-report`，不得用报告修复窗口重开 proof；annotation-gap 终态同样只允许这种 report-only 修复。

## 八、最终报告

成功时只写：

```json
{
  "status": "completed"
}
```

`blocked` 时顶层仍只含 `status` 和唯一完整 `blocker`，`blocker` 严格只含五个字段：

```json
{
  "status": "blocked",
  "blocker": {
    "failure_class": "<按本流程与交接选择现有确定值>",
    "kind": "<具体问题类型>",
    "location": "<精确 witness/declaration/proof-state 位置>",
    "message": "<完整且可诊断的问题与证据>",
    "repair_boundary": "<允许且必需的修复边界>"
  }
}
```

不在 JSON 中增加 `group`、`witness`、version、digest、changed files、命令输出、receipt、assignment、candidate paths、namespace 或 declaration metadata。controller 通过当前 delivery/accepted plan/seal 绑定 group 与 assignments；worker 用 `location`/`message` 和 `group_worker_output.md` 具体指出受影响 witness，其中 `group_worker_output.md` 对 `annotation-gap` 必填、其他终态可选。这些机器派生信息和 helper declaration metadata 无需由 owner 复制。
