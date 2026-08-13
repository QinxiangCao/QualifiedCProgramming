# demo932 Lean facade 修复说明

## 背景

`unifysl` 的 Lean 迁移已经完成到 `demo932/Interface.lean`，并且当前
`lake build Unifysl` 可以通过。现有接口在逻辑规则和定理覆盖面上基本完整，
但它采用 Lean structure/namespace 风格表达 Coq 的 module type，而后续
`annotated_simplec` 迁移原先依赖的是 Coq module composition 和 `Include`
带来的扁平命名环境。

这份文档的目标是给只负责 `unifysl` 的 agent 一个明确任务：在
`unifysl` 侧添加一个通用 `demo932` compatibility/facade 层，让下游
SimpleC 迁移更容易消费现有 `Interface.lean`，但不要把 SimpleC 专有定义
放进 `unifysl`。

## 当前 unifysl 状态

目标文件：

```text
Unifysl/LogicGenerator/demo932/Interface.lean
```

当前公开的核心对象位于 namespace：

```lean
Unifysl.LogicGenerator.demo932
```

关键结构和定义：

```lean
LanguageSig
DerivedNamesSig
PrimitiveRuleSig
LogicTheoremSig
LogicTheoremSig'
LogicTheoremSig'.default
```

`DerivedNamesSig` 目前以 namespaced definitions 公开以下对象：

```lean
DerivedNamesSig.expr
DerivedNamesSig.sepcon
DerivedNamesSig.wand
DerivedNamesSig.orp
DerivedNamesSig.andp
DerivedNamesSig.impp
DerivedNamesSig.exp
DerivedNamesSig.allp
DerivedNamesSig.emp
DerivedNamesSig.coq_prop
DerivedNamesSig.truep
DerivedNamesSig.multi_imp
DerivedNamesSig.iter_sepcon
DerivedNamesSig.iffp
DerivedNamesSig.derivable1
DerivedNamesSig.provable
DerivedNamesSig.logic_equiv
```

`LogicTheoremSig` 和 `LogicTheoremSig'` 已覆盖 Coq `demo932/Interface.v`
active declarations。此前做过名称扫描：

- Coq `LogicTheoremSig` 的 172 个 active axiom 名称，在 Lean 侧都有对应
  theorem/field。
- Coq `LogicTheoremSig'` 的 173 个 active definition 名称，在 Lean 侧都有
  对应 theorem/field。
- Coq `DerivedNamesSig` 的 derived connective/judgement 名称，在 Lean 侧都有
  对应 definition。

当前验证命令：

```bash
lake env lean Unifysl/LogicGenerator/demo932/Interface.lean
lake build Unifysl
```

二者应保持通过。

## 外侧 annotated_simplec 的需求概述

外侧 `annotated_simplec` 迁移目前无法直接使用 Lean 现有 structure API，
因为原 Coq 代码依赖 module include 后的扁平命名环境。

典型 Coq 用法来自：

```text
annotated_simplec/SeparationLogic/CommonAssertion.v
annotated_simplec/SeparationLogic/Assertion.v
annotated_simplec/SeparationLogic/ConAssertion.v
annotated_simplec/SeparationLogic/SeparationLogic.v
annotated_simplec/examples/*.v
```

外侧 agent 可能看不到这些文件，所以这里给出关键形状。

### SimpleC 的 SeparationLogicSig 形状

Coq 侧有类似下面的接口组合：

```coq
Module Type BasePredSig
  (Import Names: LanguageSig)
  (Import DerivedNames: DerivedNamesSig Names).
Parameter mstore: addr -> Z -> expr.
Parameter mstore_noninit: addr -> expr.
Axiom mstore_mstore_noninit:
  forall p v s, mstore p v s -> mstore_noninit p s.
Axiom mstore_eqm:
  forall p v v',
    Byte.eqm v v' ->
    derivable1 (mstore p v) (mstore p v').
Axiom dup_mstore_noninit:
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
End BasePredSig.

Module Type SeparationLogicSig :=
  LanguageSig <+
  DerivedNamesSig <+
  PrimitiveRuleSig <+
  LogicTheoremSig' <+
  BasePredSig.
```

注意：`BasePredSig`、`mstore`、`addr`、`Byte.eqm` 等都是 SimpleC/内存断言
层的内容，不应进入 `unifysl`。

### SimpleC 的具体实例化形状

`Assertion.SL` 在 Coq 中大致这样实例化 `demo932`：

```coq
Module Type SL <: SeparationLogicSig.

  Definition model : Type := mem.
  Definition expr := model -> Prop.
  Definition join : model -> model -> model -> Prop := mem_join.
  Definition is_unit : model -> Prop := mem_empty.

  Include DerivedNamesSig.

  Theorem unit_join : forall n : model,
    exists u : model, is_unit u /\ join n u n.
  Theorem unit_spec : forall n m u : model,
    is_unit u -> join n u m -> n = m.
  Definition join_comm :
    forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m := ...
  Definition join_assoc :
    forall mx my mz mxy mxyz : model,
      join mx my mxy ->
      join mxy mz mxyz ->
      exists myz : model, join my mz myz /\ join mx myz mxyz := ...

  Include LogicTheoremSig'.

  Arguments exp {A}.

  Definition mstore ...
  Definition mstore_noninit ...
  Theorem mstore_mstore_noninit ...
  Theorem mstore_eqm ...
  Theorem dup_mstore_noninit ...

End SL.
```

`ConAssertion.CSL` 也采用同样模式，只是 `model`、`join`、`is_unit` 换成并发
状态模型。

### SimpleC 下游希望使用的扁平名字

在 `Include DerivedNamesSig` 和 `Include LogicTheoremSig'` 后，Coq 侧下游
可以直接写：

```coq
expr
sepcon
wand
orp
andp
impp
exp
allp
emp
coq_prop
truep
multi_imp
iter_sepcon
iffp
derivable1
provable
logic_equiv
```

也可以直接写规则名：

```coq
derivable1_sepcon_comm
derivable1_sepcon_assoc1
derivable1_sepcon_mono
derivable1_sepcon_emp_l
derivable1_sepcon_emp_r
derivable1s_wand_sepcon_adjoint
derivable1s_exp_l
derivable1s_exp_r
derivable1s_allp_l
derivable1s_allp_r
logic_equiv_sepcon_comm
logic_equiv_sepcon_assoc
logic_equiv_sepcon_swap
logic_equiv_andp_assoc
logic_equiv_andp_comm
logic_equiv_andp_swap
logic_equiv_orp_comm
logic_equiv_orp_assoc
logic_equiv_coq_prop_and
logic_equiv_coq_prop_or
derivable1_iter_sepcon_flatten
derivable1_sepcon_iter_sepcon1
derivable1_sepcon_iter_sepcon2
```

并且证明脚本中常见：

```coq
rewrite derivable1_sepcon_comm.
rewrite logic_equiv_sepcon_swap.
apply derivable1_refl.
apply derivable1_trans with ...
apply derivable1_sepcon_mono.
```

Lean 不需要逐字兼容 Coq tactic 脚本，但 facade 至少应让下游能用稳定、短的
投影/别名访问这些对象。

### SimpleC 的 notation 需求

SimpleC 会自己定义 notation，形状大致是：

```coq
Notation "'emp'" := (CRules.emp).
Notation "x |-- y" := (CRules.derivable1 x y).
Notation "x --||-- y" := (CRules.logic_equiv x y).
Notation "x -* y" := (CRules.wand x y).
Notation "x --> y" := (CRules.impp x y).
Notation "x || y" := (CRules.orp x y).
Notation "x && y" := (CRules.andp x y).
Notation "x ** y" := (CRules.sepcon x y).
Notation "“ P ”" := (CRules.coq_prop P).
Notation "'TT'" := (CRules.truep).
Notation "'EX' x , p" := (CRules.exp (fun x => p)).
Notation "'ALL' x , p" := (CRules.allp _ (fun x => p)).
```

这些 notation 不应放在 unifysl facade 中；facade 只需提供 `CRules.exp`
这种可被下游 namespace/structure 投影出来的函数。

## 希望在 unifysl 侧新增的内容

建议新增文件：

```text
Unifysl/LogicGenerator/demo932/Facade.lean
```

并在需要时从 root import：

```text
Unifysl.lean
```

如果担心 root import 面过大，可以暂时不加到 `Unifysl.lean`，但文件本身必须
能独立 elaboration。

### 设计目标

新增一个通用 facade，不改变现有 `Interface.lean` 的核心 API。

推荐 namespace：

```lean
namespace Unifysl
namespace LogicGenerator
namespace demo932
namespace Facade
```

推荐提供一个包装结构，例如：

```lean
structure Context : Type ... where
  Names : LanguageSig
  DerivedNames : DerivedNamesSig Names
  Rules : PrimitiveRuleSig Names DerivedNames
  Theorems : LogicTheoremSig' Names DerivedNames Rules :=
    LogicTheoremSig'.default Names DerivedNames Rules
```

实际 universe 参数请按 `Interface.lean` 当前声明调整。此前最小 smoke test 发现
`LogicTheoremSig'` 的 `v` 有时无法由使用点自动推出，因此 facade 必须显式处理
universe，避免下游直接接触或反复手写 `LogicTheoremSig'.{u,v}`。

这不是要求修改 `LogicTheoremSig'` 本体，也不是要求把整个接口单 universe 化。
推荐做法是让 `Context` 自身带 universe 参数，并在 `Context` 的默认定理组装
入口内部显式调用 `LogicTheoremSig'.default`。如果 SimpleC 下游主要工作在
`Type 0`，可以额外提供一个 convenience alias/constructor，例如 `Context0` 或
`Context.ofType0`，但不要牺牲现有 `exp/allp` 的 universe-polymorphic 能力。

### 必须重导出的 connective/judgement

对 `ctx : Context`，提供短名函数或 abbrev：

```lean
ctx.expr
ctx.sepcon
ctx.wand
ctx.orp
ctx.andp
ctx.impp
ctx.exp
ctx.allp
ctx.emp
ctx.coq_prop
ctx.truep
ctx.multi_imp
ctx.iter_sepcon
ctx.iffp
ctx.derivable1
ctx.provable
ctx.logic_equiv
```

如果 Lean 不适合做结构投影，也可以做 namespaced defs：

```lean
Facade.expr ctx
Facade.sepcon ctx
Facade.derivable1 ctx
...
```

但推荐让 SimpleC 侧可以写类似：

```lean
namespace CRules
abbrev sepcon := ctx.sepcon
abbrev derivable1 := ctx.derivable1
...
end CRules
```

### 必须重导出的 theorem/rule

至少提供常用规则别名，以减少下游访问
`LogicTheoremSig.<name> ctx.Theorems.toLogicTheoremSig` 或
`ctx.Theorems.<field>` 的负担。

建议第一批覆盖：

```lean
derivable1s_coq_prop_r
derivable1s_coq_prop_l
derivable1_iter_sepcon_l
derivable1_iter_sepcon_r
derivable1s_allp_r
derivable1s_allp_l
derivable1s_exp_r
derivable1s_exp_l
__derivable1_provable
logic_equiv_sepcon_emp
logic_equiv_andp_truep
logic_equiv_truep_andp
logic_equiv_sepcon_comm
logic_equiv_sepcon_assoc
logic_equiv_orp_congr
logic_equiv_orp_comm
logic_equiv_orp_assoc
logic_equiv_andp_congr
logic_equiv_andp_comm
logic_equiv_andp_assoc
logic_equiv_refl
logic_equiv_symm
logic_equiv_trans
derivable1_orp_sepcon_l
derivable1_sepcon_emp_l
derivable1_sepcon_emp_r
derivable1s_wand_sepcon_adjoint
derivable1_sepcon_comm
derivable1_sepcon_assoc1
derivable1_sepcon_mono
derivable1_iffp_intros
derivable1_iffp_elim1
derivable1_iffp_elim2
derivable1_truep_intros
derivable1_orp_intros1
derivable1_orp_intros2
derivable1_orp_elim
derivable1s_truep_intros
derivable1_andp_elim1
derivable1_andp_elim2
derivable1s_impp_andp_adjoint
derivable1s_modus_ponens
derivable1s_impp_intros
derivable1_impp_refl
derivable1_axiom1
derivable1_axiom2
derivable1_refl
derivable1_trans
logic_equiv_sepcon_swap
logic_equiv_andp_swap
derivable1_exp_andp_l
derivable1_andp_exp_l
derivable1_exp_sepcon_l
derivable1_sepcon_exp_l
derivable1_iter_sepcon_flatten
derivable1_iter_sepcon_coq_prop_andp_l
derivable1_sepcon_iter_sepcon1
derivable1_sepcon_iter_sepcon2
derivable1_wand_elim1
derivable1_wand_elim2
```

It is acceptable to expose all `LogicTheoremSig` wrappers, not just this subset.
The important part is that downstream SimpleC code has a stable facade entry
point and does not need to understand the internal assembly in
`LogicTheoremSig'.default`.

### Optional instance exposure

Coq `LogicTheoremSig'` exports many typeclass instances from a module body. Lean
currently constructs them locally inside `LogicTheoremSig'.default` with `letI`;
they are not exposed independently.

For SimpleC's immediate needs, theorem fields are more important than global
typeclass search. However, if cheap and stable, facade may expose local-instance
helpers such as:

```lean
instance derivable1_refl_inst (ctx : Context) :
  Reflexive ctx.derivable1 := ctx.Theorems.derivable1_refl_inst

instance derivable1_trans_inst (ctx : Context) :
  Transitive ctx.derivable1 := ctx.Theorems.derivable1_trans_inst

instance logic_equiv_refl_inst (ctx : Context) :
  Reflexive ctx.logic_equiv := ctx.Theorems.logic_equiv_refl_inst
```

Do not add broad global instances that are not parameterized by an explicit
context; that could create instance-search ambiguity across multiple generated
interfaces.

## 边界要求

可以在 unifysl 侧做：

- `demo932` 通用 facade。
- 对现有 `Interface.lean` theorem/field 的短名投影。
- 对 `LogicTheoremSig'.default` 的 context 包装。
- 必要的 smoke tests。

不要在 unifysl 侧做：

- `BasePredSig`。
- `mstore`、`mstore_noninit`。
- `store_int`、`store_ptr`、array/string/map assertion libraries。
- `CRules`、`naive_C_Rules` 等 SimpleC 命名。
- SimpleC 的 `|--`、`**`、`&&`、`EX`、`ALL` notation。
- 依赖 `annotated_simplec`、CompCert、SetsClass、SimpleC memory model 的任何内容。

## 验收标准

1. 新文件独立通过：

```bash
lake env lean Unifysl/LogicGenerator/demo932/Facade.lean
```

2. 全库仍通过：

```bash
lake build Unifysl
```

3. 新增一个最小 smoke test，推荐放在 facade 文件末尾的 private namespace 或
单独测试文件中。测试应证明以下流程可用：

```lean
import Unifysl.LogicGenerator.demo932.Facade

namespace Smoke

open Unifysl.LogicGenerator.demo932

def Names : LanguageSig.{0} where
  model := PUnit
  join := fun _ _ _ => True
  is_unit := fun _ => True

def Derived : DerivedNamesSig Names := {}

def Rules : PrimitiveRuleSig Names Derived where
  unit_join := by
    intro n
    exact ⟨PUnit.unit, True.intro, True.intro⟩
  unit_spec := by
    intro n m u hu hj
    cases n
    cases m
    rfl
  join_comm := by
    intro m1 m2 m h
    trivial
  join_assoc := by
    intro mx my mz mxy mxyz hxy hxyz
    exact ⟨PUnit.unit, True.intro, True.intro⟩

def Ctx : Facade.Context.{0, 0} where
  Names := Names
  DerivedNames := Derived
  Rules := Rules

example :
    Ctx.derivable1 Ctx.emp Ctx.truep := by
  intro m hm
  trivial

example :
    Ctx.logic_equiv (Ctx.sepcon Ctx.emp Ctx.emp) Ctx.emp :=
  Ctx.logic_equiv_sepcon_emp Ctx.emp

end Smoke
```

The exact constructor syntax may differ depending on the final facade design;
the important point is that a downstream user can instantiate `Names`,
`Derived`, `Rules`, obtain a context, and then use short projected names and
rules.

4. Universe 封装必须有验证。至少应提供一个 smoke test 或 example，证明下游
   不需要直接写 `LogicTheoremSig'.{u,v}` 就能构造 facade context 并使用
   `ctx.exp`、`ctx.allp`、`ctx.logic_equiv_sepcon_emp` 这类对象。允许在
   `Facade.Context.{u,v}` 或 convenience constructor 上显式 universe，但不要
   把 `LogicTheoremSig'.{u,v}` 泄漏给下游 SimpleC 包装层。

5. The facade must not require importing anything outside `unifysl`.

## 实现提示

- Prefer `abbrev` for connective/judgement reexports so definitional equality
  remains friendly.
- Keep the existing `Interface.lean` API stable. Add a new layer instead of
  renaming current fields.
- If theorem names collide with existing projections, put aliases under
  `Facade.Context` namespace or use method-style projections.
- Be explicit with universe parameters if Lean cannot infer them from `exp/allp`
  use. The existing `Interface.lean` uses universes `u v`; do not accidentally
  monomorphize quantifiers unless the smoke test and downstream use justify it.
- Avoid unqualified global theorem names when they would collide with root
  `Unifysl.*` declarations. A namespaced facade is safer.

## 后续 SimpleC 侧会如何使用

完成 facade 后，SimpleC 迁移侧可以定义自己的 wrapper，例如：

```lean
namespace SimpleC.SL.Assertion

open Unifysl.LogicGenerator.demo932

def Names : LanguageSig := ...
def Derived : DerivedNamesSig Names := {}
def Rules : PrimitiveRuleSig Names Derived := ...
def Core : Facade.Context := Facade.Context.mk Names Derived Rules

namespace CRules

abbrev model := Core.model
abbrev expr := Core.expr
abbrev sepcon := Core.sepcon
abbrev emp := Core.emp
abbrev derivable1 := Core.derivable1
abbrev logic_equiv := Core.logic_equiv

theorem derivable1_sepcon_comm := Core.derivable1_sepcon_comm
theorem logic_equiv_sepcon_swap := Core.logic_equiv_sepcon_swap

-- SimpleC-only definitions start here:
def mstore : addr -> Z -> expr := ...
def mstore_noninit : addr -> expr := ...

end CRules
end SimpleC.SL.Assertion
```

Then SimpleC can add notation and memory predicates on top without asking
unifysl to know about SimpleC.
