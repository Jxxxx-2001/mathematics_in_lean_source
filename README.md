# Mathematics in Lean — 含解答与教学注释

[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) 是一本使用 [Lean 4](https://leanprover.github.io/) 交互式证明助手和 [Mathlib](https://github.com/leanprover-community/mathlib4) 学习数学证明的教程。

教材可在线阅读：[HTML 版](https://leanprover-community.github.io/mathematics_in_lean/) | [PDF 版](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf)

> 本书的 Lean 3 版本见 <https://github.com/leanprover-community/mathematics_in_lean3>

---

## 📋 项目来源

本仓库的代码整合自以下两个项目：

| 来源 | 说明 |
|------|------|
| [**imathwy/mil_0523**](https://github.com/imathwy/mil_0523) | 在原始教材基础上添加了**完整练习解答**（[`MIL/*/solutions/`](MIL/)）和**中文教学注释**，以及 Codespaces 开发环境配置 |
| [**avigad/mathematics_in_lean_source**](https://github.com/avigad/mathematics_in_lean_source) | 教材的**官方源码仓库**，包含完整的教材构建系统（Sphinx、脚本、标记语法等） |

整合后的仓库在保留官方源码构建能力的同时，额外提供了所有练习的解答文件，方便学习者对照参考。

---

## 🚀 快速开始

### 在本地使用

1. 安装 Lean 4 和 VS Code，参考[官方安装指南](https://lean-lang.org/install/)
2. 克隆本仓库：
   ```bash
   git clone https://github.com/Jxxxx-2001/mathematics_in_lean_source.git
   cd mathematics_in_lean_source
   ```
3. 获取编译好的 Mathlib：
   ```bash
   lake exe cache get
   ```
4. 在 VS Code 中打开任意 `.lean` 文件即可开始

### 在浏览器中使用（GitHub Codespaces）

如果你在安装 Lean 时遇到问题，可以直接在浏览器中使用 GitHub Codespaces：

<a href='https://codespaces.new/Jxxxx-2001/mathematics_in_lean_source' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

选择 Machine type 为 `4-core`，点击 `Create codespace`（首次启动可能需要几分钟）。

> **提示**：Codespaces 每月提供一定的免费使用时长。用完记得按 `Ctrl/Cmd+Shift+P`，输入 `stop current codespace` 停止虚拟机。也可以访问 <https://github.com/codespaces> 管理你的工作空间。

### 学习建议

我们**强烈建议**将 `MIL` 文件夹复制一份到你自己的工作目录中，在副本里完成练习。这样原始文件保持完整，也方便后续更新仓库。

解答文件位于各章的 `solutions/` 子目录中，可以用 `MIL_solutions.lean` 批量加载对照。

---

## 📖 目录结构

```
MIL/                          # Lean 源文件（按章节组织）
  C01_Introduction/
    S01_Getting_Started.lean  # 每节的练习文件
    S02_Overview.lean
    solutions/                # 对应节的解答
      Solutions_S01_Getting_Started.lean
      Solutions_S02_Overview.lean
  C02_Basics/
  ...
  C13_Integration_and_Measure_Theory/
MIL.lean                      # 练习入口文件
MIL_solutions.lean            # 解答入口文件
```

---

## 🔧 构建教材（面向开发者）

以下内容适用于想要从源码构建教材 HTML/PDF 的开发者。

### 环境准备

```bash
# 安装 Lean 依赖
lake exe cache get

# 安装 Sphinx 与 Python 依赖
pip install -r scripts/requirements.txt
```

### 构建流程

运行 `scripts/mkall.py`：
- 创建并初始化 `source/` 目录（供 Sphinx 使用）
- 创建并初始化 `user_repo/` 目录（供部署到用户仓库）
- 更新 `MIL.lean` 以匹配 `MIL/` 文件夹内容

```bash
make html       # 构建 HTML 版
make latexpdf   # 构建 PDF 版
```

部署到用户仓库：

```bash
scripts/deploy.sh <github-org> <repo-name>
```

清理构建产物：

```bash
scripts/clean.py
```

### 测试

```bash
lake build                                      # 测试所有 Lean 源文件
scripts/examples_test.py && lake build          # 测试生成的练习文件
scripts/solutions_test.py && lake build         # 测试生成的解答文件
scripts/mksection.py C03_Logic S02_The_Existential_Quantifier  # 测试单节
```

---

## 📝 Lean 源文件标记语法

源文件通过注释标记控制内容输出到三个目标：

| 标记 | 作用 |
|------|------|
| `/- TEXT: ... TEXT. -/` | 仅输出到教材 |
| `-- EXAMPLES:` | 后续行输出到练习文件 |
| `-- SOLUTIONS:` | 后续行输出到解答文件 |
| `-- BOTH:` | 后续行同时输出到练习和解答 |
| `-- OMIT:` | 后续行不输出到任何文件 |
| `-- QUOTE: ... -- QUOTE.` | 标记教材中的引用块 |
| `-- TAG: name ... -- TAG: end` | 标记可复用的引用片段 |

常见模式——练习题：

```
/- TEXT:
As an exercise, try proving the other inclusion:
BOTH: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.
```

练习文件只会看到 `sorry`，解答文件则包含完整证明。更多详情见[官方标记文档](https://github.com/avigad/mathematics_in_lean_source#markup)。

---

## 🙏 致谢与贡献

- **教材作者**：[Jeremy Avigad](https://github.com/avigad) 等 — [mathematics_in_lean_source](https://github.com/avigad/mathematics_in_lean_source)
- **解答与注释**：[imathwy](https://github.com/imathwy) — [mil_0523](https://github.com/imathwy/mil_0523)

教材仍在不断完善中，欢迎反馈和勘误。请向上游[源码仓库](https://github.com/avigad/mathematics_in_lean_source)提交 PR，或在 [Lean Zulip](https://leanprover.zulipchat.com/) 上参与讨论。
