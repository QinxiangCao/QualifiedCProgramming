# 函数指针哈希表

迁自 `/home/ltc/Coding/sac_c_parser-func-ptr/examples/hash_table/`。
采用桶数组和单向冲突链，通过函数指针提供哈希、相等比较及可选的键/值释放回调。
入口为 `ht_init`、`ht_add`、`ht_find`、`ht_remove`；分配和释放接口由头文件中的契约描述。

对应 Rocq 文件位于 `Rocq/examples/Applications_human/hash_table/`。
数学模型与手工证明迁自 `/home/ltc/tmp/ltc_annoC/examples/hash_table/`，
已将旧 `fun_CRules` 名称适配为本仓库的 `naive_C_Rules`，并使用完整模块路径。
VC、结构定义和自动证明文件由当前 `bin/linux/symexec` 重新生成。

重新生成：

```sh
dune build -j4 @gen-vcs/Applications_human/hash_table/hash_table.c --auto-promote
```

检查证明：

```sh
dune build -j4 Rocq/examples/Applications_human/hash_table/
```

迁入时 C 语法检查、符号执行及 `hash_table_lib.v` 编译通过。自动证明文件含生成器留下的 `Admitted`；
旧手工证明的复用不等于完整验证通过。

生成器已适配当前 Rocq 库，普通结构体不再生成多余的数组实例，也不再生成 `sizeA_valid`。
释放回调规格的量词类型实例化缺陷已从源码仓库修复；重新生成后，整个哈希表目录
（含 manual 与 goal-check 文件）已通过 `dune build -j4` 编译。
自动证明文件仍有生成器产生的 `Admitted`，编译通过不等于无假设的完整验证。

`ht_store_map` 及其两个 hole 谓词统一封装键等价关系与哈希兼容性。
`ht_init` 要求这两项性质，后续 add/find/remove 契约通过 map 谓词获取它们。
