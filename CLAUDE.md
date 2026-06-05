# CLAUDE.md

本文件为 Claude Code (claude.ai/code) 在此仓库中工作时提供指导。

## 项目概览

这是 **Mathematics in Lean**（MIL），一本使用 [Lean 4](https://leanprover.github.io/) 和 [Mathlib4](https://github.com/leanprover-community/mathlib4) 学习数学证明的教程。配套教材在线地址：<https://leanprover-community.github.io/mathematics_in_lean/>。

- **Lean 工具链：** `leanprover/lean4:v4.28.0`
- **Mathlib 版本：** `v4.28.0`
- **构建系统：** Lake（Lean 的构建工具）

## 常用命令

```bash
# 构建整个 MIL 项目
lake build

# git pull 后更新依赖缓存
lake exe cache get

# 检查 Lean 服务器和 mathlib 是否正确安装
# 在 VS Code 中打开任意 .lean 文件，观察状态栏中的 "Info" 指示器。
```

本项目没有独立的测试运行器或 linter —— Lean 的类型检查器本身就是验证器。`lake build` 成功即意味着所有证明正确。

## 代码架构

### 文件组织

```
MIL/                           # 所有教程内容
  Common.lean                  # 共享导入（Mathlib.Tactic 等），每个章节文件都会导入
  C01_Introduction/
    S01_Getting_Started.lean   # 第 1 章第 1 节的练习题
    S02_Overview.lean
    solutions/                 # 练习题解答（默认不被导入）
      Solutions_S01_Getting_Started.lean
      ...
  C02_Basics/
  ...
  C13_Integration_and_Measure_Theory/

MIL.lean                       # 主入口 —— 导入所有练习题文件
MIL_solutions.lean             # 解答入口 —— 导入所有解答文件
lakefile.toml                  # Lake 构建配置；构建目标为 "MIL"
lean-toolchain                 # 锁定 Lean 版本
lake-manifest.json             # 依赖锁定文件
```

### 关键模式

- **每一章**（`C01`–`C13`）包含 2–6 个节文件（如 `S01_Getting_Started.lean`）。节文件包含读者需要填写的示例和练习题。
- **解答** 存放在每章的 `solutions/` 子目录中。解答文件名以 `Solutions_` 为前缀，与节文件对应。`MIL.lean` 导入练习题文件；`MIL_solutions.lean` 导入解答文件 —— 两者永远不会同时被导入。
- **`MIL.Common`** 被所有文件导入，设置了 `Mathlib.Tactic`、`warningAsError = false` 以及常用的 delaborator。所有章节通用的导入应放在此处。
- **练习题** 以 `example`、`theorem` 或 `def` 标记，通常包含 `sorry` 表示读者需要填补证明的位置。解答文件将这些 `sorry` 替换为实际证明。
- **所有内容都在 `MIL` 命名空间下**，由 `lakefile.toml` 中的 `[[lean_lib]] name = "MIL"` 配置。

### 第三方依赖（来自 Mathlib4）

- `mathlib` — 核心数学库
- `aesop` — 证明搜索自动化策略
- `proofwidgets` — 交互式可视化
- `plausible` — 基于属性的测试
- `batteries` — 标准库扩展

## 贡献政策

**不要对此仓库提交 PR。** 这是用于学习教材的克隆/分支版本。源代码仓库位于 <https://github.com/avigad/mathematics_in_lean_source> —— 所有贡献应提交到那里。`.github/pull_request_template.md` 中已说明此政策。

## Lean 代码风格注意事项

- 优先使用 `fun a ↦ b` 而非 `λ a, b`（由 lakefile.toml 中的 `pp.unicode.fun = true` 设定）。
- 每个文件以 `import MIL.Common` 开头。
- 遵循 Mathlib4 命名规范：定理/引理使用 `snake_case`，类型/结构体使用 `CamelCase`。

---

## 行为准则

以下准则倾向于谨慎而非速度。对于简单任务，自行判断。

### 1. 先思考再编码

**不要假设。不要掩盖困惑。明确表达权衡。**

实施前：
- 明确陈述你的假设。如果不确定，就提问。
- 如果存在多种解释，将它们都列出来 —— 不要默默选择一种。
- 如果存在更简单的方法，就指出来。有理有据时可以提出异议。
- 如果有不清楚的地方，停下来。明确指出来。提问。

### 2. 简单优先

**用最少代码解决问题。不要做推测性的工作。**

- 不实现未要求的功能。
- 不为一次性代码创建抽象层。
- 不添加未被要求的"灵活性"或"可配置性"。
- 不为不可能发生的场景做错误处理。
- 如果你写了 200 行代码但 50 行就够了，重写它。

扪心自问："一位资深工程师会说这过于复杂吗？" 如果是，就简化。

### 3. 精确修改

**只改你必须改的。只清理你自己造成的混乱。**

编辑已有代码时：
- 不要"改进"旁边的代码、注释或格式。
- 不要重构没有问题的东西。
- 匹配已有的代码风格，即使你会用不同的方式写。
- 如果注意到无关的死代码，提出来 —— 但不要删除它。

当你的改动造成孤立的代码时：
- 移除因为你的改动而变得无用的导入/变量/函数。
- 除非被要求，否则不要删除已存在的死代码。

检验标准：每一行改动都应该能直接追溯到用户的需求。

### 4. 目标驱动执行

**定义成功标准。循环迭代直到验证通过。**

将任务转化为可验证的目标：
- "添加一个证明" → "确保文件通过 `lake build` 编译"
- "修复 bug" → "写一个能复现问题的测试，然后让它通过"
- "重构 X" → "确保重构前后 `lake build` 都通过"

对于多步骤的任务，给出简要的计划：
```
1. [步骤] → 验证: [检查项]
2. [步骤] → 验证: [检查项]
3. [步骤] → 验证: [检查项]
```

**关键**：Lean 文件正确的充要条件是能编译通过。`lake build` 是最终的验证标准 —— 如果它通过了，证明就是有效的。
