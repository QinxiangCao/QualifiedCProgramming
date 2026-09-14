# 普通 Assert 的放置

普通 `Assert` 只用于补出 verification 必须依赖、但 symbolic execution 在该程序点无法确定的状态。Plan 不复制普通 `Assert`；完整内容以 C annotation 为准。

## 放置规则

- 每个循环前写 `Inv Assert`，描述循环进度、仍持有的资源和稳定数学状态。
- 不要在 `Inv Assert` 前面再叠一条普通 `Assert`。
- `if` 前可以按需写普通 `Assert`，但只有分支判断或分支内验证确实缺少状态时才写。
- `return` 前不要写普通 `Assert`；由循环退出状态或当前 symbolic state 直接连接 `Ensure`。
- 其他位置只有在完全无法确定程序状态、验证必须依赖补充信息时才写。

函数体内不要用 `by local`、branch-control、普通 `Inv`、multi-inv 或 call `where` 代替这些规则。

## 保持简短

普通 `Assert` 只写下游真正要用的事实和资源。删除以下断言：

- 复制下一条 `Inv Assert` 的断言；
- 简单赋值后重复 symbolic state 的断言；
- 分支末尾只为回到循环头而重述 invariant 的断言；
- 返回前复制 `Ensure` 的断言；
- 只为暂时压住 VC、没有实际程序含义的断言。

若一个事实能由 spec、当前 guard、已有资源或循环 invariant 直接得到，就让 symbolic execution 使用它，不再增加普通 `Assert`。
