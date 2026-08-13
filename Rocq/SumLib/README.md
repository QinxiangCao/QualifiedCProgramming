# SumLib - 有限求和库

SumLib 提供有限指标集上的整数求和接口。用户把指标集写成谓词 `P : A -> Prop`，为它注册 `Finite P` 实例后，就可以统一使用 `sum P f` 表示对满足 `P` 的元素求和。

## 编译

```sh
cd Rocq/SumLib
make depend
make
```

清理编译产物：

```sh
make clean
```

## 导入方式

通常直接导入聚合文件：

```coq
From SumLib Require Import SumLib.
```

也可以按需导入单个文件：

```coq
From SumLib Require Import Sum ZRange ZRect ListMember.
```

## 文件结构

```text
SumLib/
├── Sum.v          # 核心接口：Finite、sum、通用求和性质
├── ZRange.v       # Z 半开区间上的实例和区间求和性质
├── ZRect.v        # Z 二维矩形上的实例和二维求和性质
├── ListMember.v   # 列表成员集合上的实例
├── GraphSum.v     # 图相关求和实例预留
└── SumLib.v       # 聚合导出文件
```

## 核心接口

有限指标集由 `Finite` 描述：

```coq
Class Finite {A : Type} (P : A -> Prop) := {
  enum : list A;
  enum_ok : forall x, P x <-> In x enum;
  enum_nodup : NoDup enum
}.
```

`sum P f` 表示 `Σ_{x | P x} f x`，其中 `f : A -> Z`。`enum_nodup` 保证枚举没有重复元素。

## 已提供的指标集

`ZRange.v` 注册半开区间：

```coq
sum (fun i => low <= i < high) (fun i => f i)
```

并提供带额外过滤条件的版本：

```coq
sum (fun i => low <= i < high /\ P i) (fun i => f i)
```

`ZRect.v` 注册 pair 形式的二维矩形，同时提供 pair 求和和嵌套求和之间的桥接引理。用户侧一般优先写嵌套求和：

```coq
sum (fun i => x_low <= i < x_high)
    (fun i => sum (fun j => y_low <= j < y_high)
                  (fun j => f i j))
```

`ListMember.v` 注册列表成员集合。该实例会用 `nodup` 去重，所以列表中重复出现的元素只会求和一次。
