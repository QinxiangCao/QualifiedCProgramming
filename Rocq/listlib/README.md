# ListLib - 列表操作库

本库提供列表相关的基础操作和性质证明，是算法验证中处理列表数据结构的核心工具库。

## 设计理念

本库采用分层设计，将列表操作分为两个层次：

- **基础层（Base/）**：提供基于不同视角的列表基础操作
  - **归纳视角**：基于 `cons`、`nil`、`app` 等归纳构造的列表操作
  - **位置视角**：基于位置索引（`Znth`、`Zsublist` 等）的列表访问

- **通用层（General/）**：基于基础层构建的高级列表性质和定义

## 文件结构

### Base/ - 基础层

#### `Inductive.v` - 归纳构造相关

基于列表的归纳结构提供基础引理。

#### `Positional.v` - 位置索引相关

提供基于位置索引的列表操作定义及基础性质：

**核心定义：**
- `Znth n l d`: `l`的第`n`项，如果`n`超出范围，那么返回缺省值`d`
- `Znth_error n l`: `l`的第`n`项，如果`n`超出范围，那么返回`None`
- `replace_Znth n l a`: 将`l`的第`n`项替换为`a`，如果`n`超出范围，那么返回`l`
- `replace_Znth_error n l a`: 将`l`的第`n`项替换为`a`，如果`n`超出范围，那么返回`None`
- `Zsublist lo hi l`: 提取列表`l`在区间`[lo, hi)`内的子列表，如果`lo`或`hi`为负，则视作`0`，如果`lo`或`hi`超出长度，则视作`Zlength l`

**底层性质：**
关于`Znth`, `Znth_error`, `replace_Znth`, `replace_Znth_error`, `Zsublist`的证明。

### General/ - 通用层

#### `Length.v` - 列表长度

提供列表长度的定义及其与各种列表操作的关系：

**核心定义：**
- `Zlength l`: 列表长度的 Z 类型版本

**基本性质：**
- `Zlength` 与 `app`、`cons`、`nil` 的性质
- `Zlength` 与 `Znth`、`replace_Znth`、`Zsublist` 的性质

#### `Presuffix.v` - 前缀、后缀与子列表

定义前缀、后缀、子列表关系及其性质：

**核心定义：**
- `is_prefix l1 l2`: `l1` 是 `l2` 的前缀（存在 `l3` 使得 `l2 = l1 ++ l3`）
- `is_suffix l1 l2`: `l1` 是 `l2` 的后缀（存在 `l3` 使得 `l2 = l3 ++ l1`）
- `is_sublist l1 l2`: `l1` 是 `l2` 的子列表

**基本性质：**
- `is_prefix`, `is_suffix`, `is_sublist` 与 `app`、`cons`、`nil` 的性质
- `is_prefix`, `is_suffix`, `is_sublist` 与 `Znth`、`replace_Znth`、`Zsublist` 的性质

#### `IndexedElements.v` - 索引元素列表

定义通过索引列表从原列表中提取元素的操作：

**核心定义：**
- `is_indexed_elements l il l0`: 从列表 `l` 中按索引列表 `il` 依次取出元素得到 `l0`
- `sincr il`: 索引列表严格递增
- `is_subsequence l1 l2`: `l1` 是 `l2` 的子序列（可跳过元素）

**基本性质：**
- `is_indexed_elements` 与 `app`、`cons`、`nil` 的性质
- `is_indexed_elements` 与 `Znth`、`replace_Znth`、`Zsublist` 的性质

#### `Forall.v` - Forall 谓词扩展

提供 `Forall` 和 `Forall2` 谓词的扩展引理：

**基本性质：**
- `Forall2` 与 `app`、`cons`、`nil` 的性质
- `Forall2` 与 `Znth`、`replace_Znth`、`Zsublist` 的性质

## 补充
底层文件中放索引自身的性质；每一种通用定义都拥有独立的文件，文件内分别有该定义与cons/app和索引之间的证明。
通用层之间的交互，例如Forall2和map的交互，Presuffix和Length的交互以及IndexedElements和Forall2的交互等等，目前放在依赖关系最高一层的文件中。