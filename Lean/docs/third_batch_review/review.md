# 第三批部分库的独立复核

只读接口复核结果：未发现需要修复的语义偏差、源 Qed 前提增加、结论弱化或新增数学公理。

仓库根目录：/Users/sheringham/Desktop/qcp_lean/qcp-binary-democases

检查范围：逐项对照 P058 全部 17 个模型定义及 39 个公开 Qed；P046 全部 13 个模型定义及 31 个公开 Qed。声明名称集合分别精确一致（无缺少、无额外公开 theorem）。同时阅读关键证明构造、共享列表/整数/MaxMin 接口、案例 namespace 边界及既有 library_audit。P053 仅复核 ArrangementSpec/Spec、terminal_frequency_summary_implies_Spec 与迁移报告的表述边界。未修改仓库文件，未重跑已完成构建。

P058 Logo Turtle：
- Lean .../examples_shard00/P058_132C_logo_turtle_lib.lean:16、24、38、45、52 对应 Coq .../P058_132C_logo_turtle_lib.v:6、17、37、52、64。ChangedExactly 保留逐命令非负操作次数、总和恰好 n 及次数奇偶对应命令的关系；没有替换成只要求修改次数不超过 n。TurtleState/TurtleEnd 仍以长度为 commands+1 的真实轨迹描述执行，初态和所有状态 Znth 默认值均为 (0,1)，命令默认为 0。
- Lean:57、59、71、75 保留宽度 2*Zlength+1、flips/direction/slot 的索引、方向 0/1 对应真实方向 1/-1 及转移排名。Lean:720 的 complete_reachable_iff 保留原双向等价及完整边界/字符表前提（Coq:976），反向通过拆出最后一条命令和此前轨迹构造前驱，并未把可达性当额外假设。
- Lean:611、634 与 Coq:1351、1431 的压缩/扩展接口一致。压缩以各次数 mod 2 构造 marks，扩展把偶数差额放回第一个命令；原 commands 非空、差额非负与奇偶前提都保留。
- Lean:776 对应 Coq:1670；最终规格仍要求最大值的上界与取得者。证明分别构造终态到候选、候选到终态的关系；answer=0 分支也用实际 ChangedExactly/TurtleState 的存在性补取得者，没有以空集合的默认最大值代替。原 Pre、LayerMeaning、AnswerPrefix 三项前提均保留。

P046 Character Swap：
- Lean .../examples_shard09/P046_1243B2_character_swap_lib.lean:18、25、49、60、64 对应 Coq .../P046_1243B2_character_swap_lib.v:9、13、51、70、78。CrossSwap 仍为跨两字符串交换；SwapsWork/SwapTrace 的所有状态读取默认值为 ([],[])，操作读取默认为 (0,0)，轨迹长度/初态/逐步 CrossSwap/终态均保留。OperationLists 保留 0-based 数学操作到 1-based 输出编号的 +1。
- Lean:31 的 Pre 仅 source≠target 与原 Coq:18 一致；原 Coq 注释已说明长度与字符范围在 solver Require 给出，不能把它误判为 Lean 删除前提。最终成功定理 Lean:369 / Coq:827 仍显式接收不同输入、长度相等、i 到末尾和 RepairState；非空操作数从不同输入与真实轨迹推导，并无新增“操作非空”假设。
- Lean:267、283 对应 Coq:542、575，一次/两次交换后的嵌套 replace_Znth、操作追加顺序、i+1 和各边界前提一致。Lean:327 对应 Coq:727 的逐步计数守恒保留完整轨迹量化；失败分支通过未匹配字符导致奇数总频次，与 CombinedEven 矛盾。
- CountedPrefix/CombinedEven 用 Lean List.count 替代 Coq count_occ，计数仍为 Nat 后嵌入 Int；Z.modulo 与 Z.rem 仍明确区分，只在非负计数前提下转换。

共享接口及作用域：
- Rocq/listlib/Base/Positional.v:10、28、34 与 Lean/auxlibs/AUXLib/ListLib/Base.lean:101、115、121 一致：Znth=nth/getD(toNat index)，replace_Znth 同样用 toNat，sublist=先 take hi 再 drop lo。特别是负下标经 toNat 变 0 的原边缘语义没有改变；需要读写有效位置的 Qed 保留了非负/上界前提。
- Rocq/MaxMinLib/MaxMin.v:119 与 Lean/maxminlib/MaxMinLib/MaxMin.lean:128 都要求实际存在最大值取得者。
- Lean/auxlibs/AUXLib/ZParity.lean:8 的 Z.even 用 mod 2 定义，even_spec 给出 2*k 表征，覆盖负整数；P058 的共享奇偶接口没有引入案例前提或公理。
- 两个案例的模型及所有源公共 Qed 全部留在自身 ..._<case>_lib namespace；新增构造辅助 theorem 为 private。P046 的 Some/None/_Prod_Z_Z/fst/snd 只是该案例 namespace 内的透明别名（Lean:12–16），未注入共享根 namespace。
- 两个既有 library_audit（P058:86–89，P046:70–73）逐声明递归 collectAxioms，白名单仅 propext/Classical.choice/Quot.sound；库源码没有 sorry/axiom/opaque。沿用父任务给出的已通过日志，本次未重跑。

P053 Pinkie：
- Coq .../examples_shard00/P053_1393C_pinkie_pie_eats_patty_cakes_lib.v:21 定义 ArrangementSpec 为排列后的最小相等元素间距的最大值；:53 定义 Spec 为完整频率表的闭式公式。Lean 同文件:23、37 分别忠实保留这两个独立定义；Z.div 保留原 Coq 整数除法语义。
- Coq:59 / Lean:42 的 terminal_frequency_summary_implies_Spec 仅把完整频率概要作为见证装入 Spec，不证明 ArrangementSpec。检索本例 Coq/Lean/C 文件，ArrangementSpec 仅见于各自 lib 定义，没有 Spec→ArrangementSpec 或等价桥接。
- Lean/docs/llm_bench_third_batch_migration.md:20 及 Lean/docs/migration_inconsistencies.md:412 已明确披露上述边界，未夸大。因此“源 Qed 全迁移”可以成立，但不能据此宣称已独立证明排列最优性公式；这是源规格/源证明边界，不是这次 Lean 迁移新引入的缺陷。

局限：本次是源码语义和公开接口逐项人工复核，不是机械化的 Coq↔Lean 定义等价证明；没有重新验证共享库全部定理或独立审计 C 前端生成器。之前的 Lean 内核构建/递归公理审计作为已有证据使用。报告未把继承的 auto Admitted 计为新完成证明。

逐条源 Qed 对照附录：
[P058_132C_logo_turtle-api-review.txt](P058_132C_logo_turtle-api-review.txt)
[P046_1243B2_character_swap-api-review.txt](P046_1243B2_character_swap-api-review.txt)
