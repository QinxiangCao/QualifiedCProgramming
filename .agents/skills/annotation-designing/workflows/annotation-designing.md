# Annotation 设计、填写与修正流程

一个 run 只使用一个 annotation owner：

    读 handoff、题意和当前文件
      -> 写自然语言 spec
      -> 写 Rocq spec 与 C function spec
      -> 复用核心 predicate，填写最小 loop invariant
      -> formal-case-lib-design
      -> symexec
      -> 修正第一个失败点
      -> formal-case-lib
      -> completed

Agent 编写的 function spec、必要 predicate、C body annotation、case-lib definition/lemma 和 annotation_plan.json 在当前 attempt 内共同修改。用户提供的 spec 只在用户确认并执行 unfreeze 后修改。

## 1. 输入与写入边界

首次 attempt 读取：

- 当前 agent_input.md；
- problem context；
- 目标 C；
- canonical formal_case_lib；
- 当前 generated manual；
- annotation_plan.json。

Retry 还读取 failed_vcs 的 source attempt、VC name/parent、annotation location、sealed manual 和 old gap，以及 handoff 列出的原始 blocker。

只写：

- 目标 C 中的 function spec、Inv Assert 和必要的普通 Assert；
- policy 为 present 或 create 时的 canonical formal_case_lib；
- 当前 attempt 的 annotation_plan.json、agent_output.md 和 agent_report.json；
- 由 handoff 中 symexec 命令统一刷新的 generated files。

不改普通 C 代码、proof manual、controller state、group 文件、公共库或其他 case。不写 proof，不增加 Admitted、Axiom 或禁用 lemma。formal_case_lib policy 为 absent 时保持候选路径不存在。

## 2. 从题意生成 spec

Spec 的来源是题目描述、输入格式、输出格式和用于消除歧义的样例说明。C 实现只用于确认参数、资源和 helper 调用关系。题解和算法提示不决定 spec。

先写：

    Signature
      单个 case 的函数名、参数类型和返回类型

    Preconditions
      输入范围、长度和输入之间的关系

    Output
      输入与正确输出之间的完整数学关系

输出唯一时直接定义结果值；允许多个答案时定义 Valid inputs out。输出是一串操作时，定义单步效果和整串操作后的状态。多组输入不进入单个 case 的核心 spec。

再写同义的 Rocq：

- Pre inputs : Prop 表达输入条件；
- Spec inputs out : Prop 表达输出关系；
- 只有名称明显改善题意表达时才增加 helper definition。

顶层 spec 只说明结果是什么。算法分类、闭式推导、循环变量、DP 转移、scratch table 和数据结构构造过程不进入顶层 spec。题目隐含但没有作为输入给出的对象在 Spec 中用 exists 直接量化。

常见表达：

- 闭式结果：out = expression；
- 计数：out = #(fun x => P x)；
- 最小值或最大值：复用 min_value_of_subset 或 max_value_of_subset；
- 任意合法结果：Valid inputs out；
- 同一返回类型中的特殊值：直接分支；
- 不同形状的结果：使用已有的 Inductive、option 或 sum；
- 总有定义的单步操作：apply_op 与 fold；
- 关系式单步操作：关系组合。

数值使用 Z。有顺序的对象使用 list；无顺序的选择使用集合谓词。逐元素条件优先使用 Forall；需要位置或对应关系时使用 Znth 或 Forall2。

最后映射到 C：

- With 引入资源对应的逻辑值；
- Require 直接写输入范围、长度、overflow 条件和输入资源；
- Ensure 调用数学结果 predicate 并归还资源；
- helper 只承诺调用方实际使用的抽象性质。

自然语言 Output、Rocq Spec 和 C Ensure 必须同义。

## 3. 复用 predicate

写新 definition 前搜索当前 dependency、canonical case lib 和公共库。优先复用：

- 数组资源：IntArray::full、seg、undef_seg 及对应 family；
- list：Zlength、Znth、sublist、replace_Znth；
- 元素和对应关系：Forall、Forall2；
- 成员、互异和重排：In、NoDup、Permutation；
- 单调性：当前依赖已有的一套 increasing/decreasing 或 mono 系列；
- 计数、求和、最值：#、sum、SumLib、min_value_of_subset、max_value_of_subset；
- 图：valid_vpath、reachable。

以下内容直接写现有表达：

- Occurs := In 一类同义别名；
- 只包装一个范围或等式的 predicate；
- InputValid、SizeSafe 一类输入条件集合；
- 对排列、单调性、求和、最值或可达性的重新定义；
- 只记录临时变量和循环控制状态的 predicate；
- 重放当前 C 步骤的 Fixpoint 或状态转换。

核心 predicate 的组合也直接使用，不再增加只做嵌套转发的 wrapper。例如 `Permutation input output /\ increasing output`、`sum (sublist lo hi l)` 和已有最大值关系可以直接进入 spec 或 invariant。题目输出或跨函数接口需要一个名称时只保留一层 case predicate，helper 和循环统一引用它。

新 predicate 只在以下条件下保留：

- 表达题目、helper 接口或循环中的明确数学性质；
- 核心 predicate 的直接组合不足以清楚表达；
- 名称能清楚说明题目或接口，或能替代多处重复公式；
- 参数只包含解释该性质需要的逻辑对象；
- spec、helper 和 invariant 复用同一个定义。

只使用一次但名称直接说明题目概念时可以保留；只包装一个范围、等式或已有 predicate 时不保留。

空间 ownership 使用已有 array、string、list 或结构体 predicate；pure predicate 只表达数学性质。

## 4. Function spec 与 loop invariant

从顶层函数向 helper 写 With、Require 和 Ensure。顶层函数直接连接题目 Spec；helper 的 Ensure 只给出 caller 使用的结果。

每个循环先写一句数学进度，再写 Inv Assert：

    当前进度
    + 下一次访问和运算需要的范围
    + 仍存活的资源
    + 必要的 @pre bridge
    + 一个已有或必要的新数学 predicate

不要把函数入口条件整段复制到每个 invariant。IntArray::full 和 seg 已带有自身长度及区间事实，不重复写这些资源已经给出的 Zlength 或非负条件。数组访问需要的实际下标范围仍直接写出。

n == n@pre 只用于值从入口到当前点未改变的变量。写出 bridge 后，同一 assertion 的范围、资源和数学性质统一使用当前变量名。

每个循环前只有一条 Inv Assert。普通 Assert 只补 symbolic execution 无法确定且下游必须使用的状态；可按需放在 if 前，不放在 return 或 Inv Assert 前。

## 5. annotation_plan.json

Plan 不复制 C annotation 或 case lib，只保存简短摘要：

    {
      "version": 2,
      "status": "ready",
      "function_specs": [
        {"name": "query", "meaning": "返回输入区间的最大值"}
      ],
      "loop_invariants": [
        {"location": "query: power loop", "progress": "pow 是不超过区间长度的当前二次幂"}
      ],
      "new_predicates": [
        {
          "name": "SparseTableBuilt",
          "meaning": "表中有效单元表示对应区间的最大值",
          "why_needed": "build 与 query 共同使用该表语义"
        }
      ],
      "vc_comparisons": []
    }

function_specs 对每个已写 C spec 的函数记录一句含义。loop_invariants 对每个 lexical loop 记录一句数学进度。new_predicates 只列当前 case 实际新增的 predicate；完全复用公共接口时保持空列表。

## 6. 检查与 retry

每轮完整修改后按 handoff 顺序运行：

1. coq-check --target-kind formal-case-lib-design；
2. symexec；
3. policy 为 present/create 时运行 coq-check --target-kind formal-case-lib。

根据第一个失败 VC 修改对应的 spec、invariant、资源或 lemma，再重跑。Generated files 只由 symexec 更新。

首次 attempt 的 vc_comparisons 为空。Retry 对每个 failed VC 记录：

    {
      "source": {
        "attempt": "<source attempt>",
        "name": "<old VC>",
        "annotation_location": "<C annotation point>"
      },
      "current": ["<current VC>"],
      "old_gap": "<missing fact or resource>",
      "change": "<spec, invariant, resource, or lemma change>",
      "result": "resolved"
    }

直接读取 sealed old manual 和 current manual，比较命题的 conclusion、pure premises、spatial resources、existential 和 witness。旧 VC 改名或拆分时，current 列出承担原责任的全部 VC。名称消失本身不表示缺口已经解决。

result 为 unresolved 时继续在当前 attempt 修改。所有 failed VC 都为 resolved 后再把 plan 设为 ready。

## 7. 输出与停止

agent_output.md 简短记录本轮修改和 VC comparison。成功的 agent_report.json 只写：

    {"status": "completed"}

用户 spec 修改方案只写 agent_output.md，不写 terminal report。Tool blocker 和 workflow 要求的结构化 blocker 使用 handoff 给出的字段。

写 terminal report 后停止修改，通知 main 执行原 finalize_invocation。若返回 report-repair-required，在同一 owner、attempt 中按 message 修正并重跑原 invocation。不要自行 accept、prove、merge、apply 或 final-check。
