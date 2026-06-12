/- TEXT:
入门指南
--------

本书的目标是教你使用 Lean 4 交互式证明助手来形式化数学。
它假设你了解一些数学，但不需要很多。
虽然我们将涵盖从数论到测度论和分析的例子，
但我们会侧重于这些领域中较为初等的部分，
如果你对它们不熟悉，希望你能在学习过程中逐步掌握。
我们也不预设你有任何形式化方法的背景。
形式化可以看作一种计算机编程：
我们将用一种规范的语言（类似于编程语言）来书写数学定义、定理和证明，
而 Lean 能够理解这种语言。
作为回报，Lean 提供反馈和信息，
解释表达式并保证它们是良构的，
最终验证我们证明的正确性。

你可以从
`Lean 项目页面 <https://leanprover.github.io>`_
和
`Lean 社区网页 <https://leanprover-community.github.io/>`_
了解更多关于 Lean 的信息。
本教程基于 Lean 庞大且不断增长的库 *Mathlib*。
我们还强烈建议你加入
`Lean Zulip 在线聊天群组 <https://leanprover.zulipchat.com/>`_
（如果还没有的话）。
在那里你会找到一个活跃而友好的 Lean 爱好者社区，
他们乐于回答问题并提供精神支持。

虽然你可以在线阅读本书的 pdf 或 html 版本，
但它被设计为交互式阅读，
在 VS Code 编辑器内运行 Lean。
要开始：

1. 按照
   `安装指南 <https://lean-lang.org/install/>`_
   安装 Lean 4 和 VS Code。

2. 点击 VS Code 右上角的全称符号获取仓库，
   选择 `Open Project`、`Download Project` 和 `Mathematics in Lean`。

3. 本书的每一节都有一个关联的 Lean 文件，包含示例和练习。
   你可以在 ``MIL`` 文件夹中找到它们，按章节组织。
   我们强烈建议你复制该文件夹，在副本中实验并完成练习。
   这样保留了原始文件，并且在仓库更新时也更容易同步（见下文）。
   你可以将副本命名为 ``my_files`` 或任何你喜欢的名字，
   并用它来创建你自己的 Lean 文件。

此时，你可以按如下方式在 VS Code 的侧面板中打开教科书：

1. 输入 ``ctrl-shift-P``（macOS 上为 ``command-shift-P``）。

2. 在出现的栏中输入 ``Lean 4: Docs: Show Documentation Resources``，
   然后按回车。（一旦它在菜单中高亮显示，你就可以按回车选择它。）

3. 在打开的窗口中，点击 ``Mathematics in Lean``。

或者，你也可以在云端运行 Lean 和 VS Code，
使用 `Codespaces <https://github.com/codespaces>`_。
你可以在 Github 上的 Mathematics in Lean
`项目页面 <https://github.com/leanprover-community/mathematics_in_lean>`_
找到相关说明。我们仍然建议按上述方式在 ``MIL`` 文件夹的副本中工作。

本教科书及其关联的仓库仍在开发中。
你可以通过在 ``mathematics_in_lean`` 文件夹中输入 ``git pull``
然后 ``lake exe cache get`` 来更新仓库。
（这假设你没有修改 ``MIL`` 文件夹的内容，
这就是我们建议制作副本的原因。）

我们希望你在阅读教科书时完成 ``MIL`` 文件夹中的练习，
教科书中包含了解释、说明和提示。
书中经常会包含示例，比如这个：
TEXT. -/
-- QUOTE:
#eval "Hello, World!"
-- QUOTE.

/- TEXT:
你应该能够在关联的 Lean 文件中找到相应的示例。
如果你点击该行，VS Code 将在 ``Lean InfoView`` 窗口中显示 Lean 的反馈，
如果你将光标悬停在 ``#eval`` 命令上，
VS Code 将在弹出窗口中显示 Lean 对此命令的响应。
我们鼓励你编辑文件并尝试自己的示例。

本书还提供了大量具有挑战性的练习供你尝试。
不要匆匆略过这些！
Lean 的核心是*交互式地做*数学，而不仅仅是阅读它。
完成练习是该体验的核心部分。
你不必做完所有练习；当你觉得已经掌握了相关技能时，可以随时继续前进。
你随时可以将自己的解答与每节关联的 ``solutions`` 文件夹中的解答进行比较。
TEXT. -/
