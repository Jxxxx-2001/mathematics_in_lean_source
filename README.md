# Mathematics in Lean — 含解答与注释版本

[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) 是一本使用 Lean 4 交互式证明助手学习数学证明的教程。

此仓库 fork 自 [avigad/mathematics_in_lean_source](https://github.com/avigad/mathematics_in_lean_source)，是教材的**源码仓库**。与原版相比，本仓库额外包含：

- **完整练习解答** ([`MIL/*/solutions/`](MIL/)) — 所有章节每道练习题的解答
- **教学注释** — 在 Lean 源文件中嵌入了中文教学批注
- **开发环境配置** — `.devcontainer/` 支持 Codespaces 开箱即用；`CLAUDE.md` 辅助 AI 工具协作

---

## 面向学习者：直接使用本仓库

如果你只是想学习教材、完成练习并对照解答：

1. 安装 Lean 4 和 VS Code，参考[官方安装指南](https://lean-lang.org/install/)
2. 克隆本仓库
3. 运行 `lake exe cache get` 获取编译好的 Mathlib
4. 在 VS Code 中打开任意 `.lean` 文件即可开始

教材可在线阅读：[HTML 版](https://leanprover-community.github.io/mathematics_in_lean/) | [PDF 版](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf)

解答文件位于各章的 `solutions/` 子目录中，可用 `MIL_solutions.lean` 批量加载。

> **建议**：复制 `MIL` 文件夹到你自己的工作目录，在副本中练习，保留原始文件作为参考。

---

## 面向开发者：构建教材

以下是原版源码仓库的构建说明。

### 环境准备

```bash
# 安装 Lean 依赖
lake exe cache get

# 安装 Sphinx 与 Python 依赖（用于构建 HTML/PDF）
pip install -r scripts/requirements.txt
```

### 构建流程

运行 `scripts/mkall.py`：
- 创建并初始化 `source/` 目录（供 Sphinx 使用）
- 创建并初始化 `user_repo/` 目录（供部署到用户仓库）
- 更新 `MIL.lean` 以匹配 `MIL/` 文件夹内容

然后使用 Sphinx 构建：

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

### 项目结构

```
MIL/                  # Lean 源文件（按章节组织）
  C01_Introduction/   # 每章一个文件夹，以 "C" + 章节编号开头
    C01_Introduction.rst    # 章节 RST 头部
    S01_Getting_Started.lean # 节文件，以 "S" + 节编号开头
    solutions/              # 解答文件
sphinx_source/        # Sphinx 文档源文件
user_repo_source/     # 用户仓库模板文件
scripts/              # 构建与部署脚本
```

### Lean 源文件标记语法

源文件通过注释标记控制内容输出到三个目标：
- **教材源文件** (Sphinx)
- **练习文件** (用户仓库，含 `sorry`)
- **解答文件** (用户仓库，含完整证明)

常用标记：

| 标记 | 作用 |
|------|------|
| `/- TEXT: ... TEXT. -/` | 仅输出到教材 |
| `-- EXAMPLES:` | 后续行输出到练习文件 |
| `-- SOLUTIONS:` | 后续行输出到解答文件 |
| `-- BOTH:` | 后续行同时输出到练习和解答 |
| `-- OMIT:` | 后续行不输出到任何文件 |
| `-- QUOTE: ... -- QUOTE.` | 标记教材中的引用块 |
| `-- TAG: my_tag ... -- TAG: end` | 标记可复用的引用片段 |

详细说明见下方「标记语法完整参考」部分。

### 测试

```bash
# 测试所有 Lean 源文件
lake build

# 测试生成的练习文件
scripts/examples_test.py && lake build

# 测试生成的解答文件
scripts/solutions_test.py && lake build

# 测试单节
scripts/mksection.py C03_Logic S02_The_Existential_Quantifier
```

---

## 标记语法完整参考

以下是原版 `README` 中的完整标记语法说明，保留作为参考。

*(以下内容来自原版仓库 README)*

The Lean files in the `MIL` folder generate three types of files:
- Source files for the Sphinx textbook.
- Files with examples (and exercises) for the user repository.
- Files with solutions for the user repository.
A line of text from the Lean file may go to any combination of these destinations simultaneously,
or nowhere at all, as determined by simple markup directives in the file.

When `scripts/mkall.py` starts processing a file,
it sends output to both the associated examples file and the associated solutions file by default.
This makes sense, for example, for the import lines.

The following markup specifies material for the textbook:
```
/- TEXT:
Stuff for the textbook goes here.
TEXT. -/
```
The lines between the comments are sent only to the associated Sphinx source file.

After the line `TEXT. -/`, by default, lines of text are sent only to the
examples file.
You can replace the last line with `EXAMPLES: -/`, which has the same effect,
`SOLUTIONS: -/` to send the lines to the solutions file,
`BOTH: -/` to send the lines to the both files,
or `OMIT: -/` to send the lines to neither.

You can subsequently modify the behavior with the additional comment lines
`-- EXAMPLES:`, `-- SOLUTIONS:`, `-- BOTH:`, and `-- OMIT:`.
The behavior stays in effect until another directive changes it.

While the script is processing lines of Lean code, you can specify that a sequence of lines
should be added to the textbook as a block quote by enclosing it as follows:
```
-- QUOTE:
example : 1 + 1 = 2 := by rfl
-- QUOTE.
```
Note the use of the period to mark the end of the quote.

In such a quote block, any lines that are designated to go only to the solutions file are not
included in the quote. Thus you can only quote lines that are sent to the examples file,
sent to both the examples and solutions files, or omitted from both.
The behavior of the `QUOTE` directives is otherwise independent of the behavior of the
`EXAMPLES`, `SOLUTIONS`, `BOTH`, and `OMIT` directives.
For example, you can switch output from the examples file to both the examples and solutions
file in the middle of a quote.
It doesn't make a difference whether one of the latter directives occurs just before or
just after a `QUOTE` directive.

You can also use `/- EXAMPLES:`, `/- SOLUTIONS:`, `/- BOTH:`, and `/- OMIT:` to put text
in a block comment that is sent to one of the files accordingly.
This provides a handy way to specify a `sorry` in an examples file
that is replaced by a solution in the solution file.
Here's an example of how these are used:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

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
The second text block represents a common idiom for presenting exercises:
after the textbook prose, a `theorem` or `example` line is sent to both the examples
and the solutions file.
The examples file contains only a `sorry`, whereas the solutions file contains the full solution.
The solution is checked by Lean in the source file, but it is not included in the quote.

Note also the useful convention that if a blank line is needed in the examples or
solutions file, it is specified *after* the relevant segment, so that the next
time output is enabled no blank line is needed.
So, in the example above, there is no blank line before or after `-- QUOTE:`
because we assume that prior input has already inserted a blank line,
but there is a blank line after `-- QUOTE.`

It is common to use sections to declare and scope variables in the examples and solutions
files, but to omit the section commands from quote.
Thus you might use the following pattern:
```
/- TEXT:
Here is an example of the way that ``rintro`` is used:
BOTH: -/
section
variable (s t u : Set α)

-- EXAMPLES:
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

```
Just make sure that, later in the file, the matching `end` and a blank line after are sent to
both outputs.

The weird pair of characters `αα` in a Lean input file is simply deleted from any
output produced by the script.
This is a little hack that allows you to produce the same identifier in the examples
and solutions files. For example, the exercise above could have been written
as follows:
```
/- TEXT:
As an exercise, try proving the other inclusion:
EXAMPLES: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem fooαα : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu

```
The theorem is named `foo` in both the examples and the solutions, but Lean doesn't
complain about a duplicate identifier in the source file.

Finally, there is a mechanism that allows you to quote any part of the file
in the textbook, before or after it appears in the Lean source file.
This can be used, for example, to present a long proof and then refer back to parts of it.
Encode the lines you want to quote with a pair of tags:
```
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
-- TAG: my_tag
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- TAG: end
```
The first tag can have any label you want in place of `my_tag`, whereas the second should
be exactly as shown. Adding the line
```
-- LITERALINCLUDE: my_tag
```
in the middle of a text block anywhere in the file will insert the tagged text as a
block quote in the textbook,
using a Sphinx directive that is designed for exactly that purpose.

---

## 贡献与反馈

教材仍在不断完善中，欢迎反馈和勘误。请向[上游仓库](https://github.com/avigad/mathematics_in_lean_source)提交 PR。

也可以在 [Lean Zulip](https://leanprover.zulipchat.com/) 上找到我们。
