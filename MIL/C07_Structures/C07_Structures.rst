.. _structures:

结构
====

现代数学不可或缺地使用代数结构，
它们封装了可以在多种情境下实例化的模式。
这门学科提供了多种方式来定义此类结构并
构造具体的实例。

因此，Lean 提供了相应的方式来
形式化地定义结构并使用它们。
你已经在 Lean 中见过代数结构的例子，
例如环和格，它们在
:numref:`第 %s 章 <basics>` 中讨论过。
本章将解释你在那里看到的
神秘方括号标注
``[Ring α]`` 和 ``[Lattice α]``。
它还将向你展示如何自己定义和使用
代数结构。

如需更多技术细节，你可以参考 `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_，
以及 Anne Baanen 的论文 `Use and abuse of instance parameters in the Lean mathematical library <https://arxiv.org/abs/2202.01629>`_。
