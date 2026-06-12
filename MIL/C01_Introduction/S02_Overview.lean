import MIL.Common

open Nat

-- SOLUTIONS:
-- 本节没有练习。
/- TEXT:
概览
----

简单地说，Lean 是一个用于在称为*依赖类型论*的形式语言中
构建复杂表达式的工具。

.. index:: check, commands ; check

每个表达式都有一个*类型*，你可以使用 `#check` 命令来
打印它。
有些表达式的类型如 `ℕ` 或 `ℕ → ℕ`。
这些是数学对象。
TEXT. -/
-- 这些是数据。
-- QUOTE:
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f
-- QUOTE.

/- TEXT:
有些表达式的类型为 `Prop`。
这些是数学命题。
TEXT. -/
-- 这些是命题，类型为 `Prop`。
-- QUOTE:
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem
-- QUOTE.

/- TEXT:
有些表达式具有类型 `P`，其中 `P` 本身的类型是 `Prop`。
这样的表达式是命题 `P` 的一个证明。
TEXT. -/
-- 这些是命题的证明。
-- QUOTE:
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard
-- QUOTE.

/- TEXT:
如果你设法构造了一个类型为 ``FermatLastTheorem`` 的表达式，
并且 Lean 接受它作为该类型的一个项，
那么你就完成了一件非常了不起的事情。
（使用 ``sorry`` 是作弊，Lean 知道这一点。）
所以现在你知道了游戏规则。
剩下要学的就是技巧了。

本书与配套教程
`Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean4/>`_
互补，后者对 Lean 的底层逻辑框架和核心语法提供了更全面的介绍。
*Theorem Proving in Lean* 适合那些喜欢在使用新洗碗机之前
先从头到尾阅读用户手册的人。
如果你是那种喜欢先按下*启动*按钮，
然后再琢磨如何激活强力洗涤功能的人，
那么从这里开始并随时回头查阅
*Theorem Proving in Lean* 更为合理。

*Mathematics in Lean* 与 *Theorem Proving in Lean* 的另一个区别在于，
这里我们更加注重*策略*（tactics）的使用。
鉴于我们试图构建复杂的表达式，
Lean 提供了两种方式：
我们可以直接写出表达式本身
（即合适的文本描述），
或者向 Lean 提供如何构造这些表达式的*指令*。
例如，下面的表达式表示了一个证明，
证明如果 ``n`` 是偶数，那么 ``m * n`` 也是偶数：
TEXT. -/
-- 这里是一些证明。
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩
-- QUOTE.

/- TEXT:
该*证明项*可以压缩为一行：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
-- QUOTE.

/- TEXT:
以下是同一个定理的*策略风格*证明，其中以 ``--`` 开头的行
是注释，因此会被 Lean 忽略：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- 设 `m` 和 `n` 是自然数，并假设 `n = 2 * k`。
  rintro m n ⟨k, hk⟩
  -- 我们需要证明 `m * n` 是某个自然数的两倍。我们来证明它是 `m * k` 的两倍。
  use m * k
  -- 替换 `n`，
  rw [hk]
  -- 现在结论显而易见。
  ring
-- QUOTE.

/- TEXT:
当你在 VS Code 中逐行输入这样的证明时，
Lean 会在一个单独的窗口中显示*证明状态*，
告诉你已经建立了哪些事实，以及还需要完成
哪些任务来证明你的定理。
你可以通过逐行步进来回放证明，
因为 Lean 会持续显示光标所在位置的证明状态。
在这个例子中，你会看到
证明的第一行引入了 ``m`` 和 ``n``
（如果需要，我们可以在那时重命名它们），
并将假设 ``Even n`` 分解为
一个 ``k`` 以及 ``n = 2 * k`` 的假设。
第二行 ``use m * k``
声明我们将通过证明 ``m * n = 2 * (m * k)`` 来表明
``m * n`` 是偶数。
下一行使用 ``rw`` 策略
在目标中将 ``n`` 替换为 ``2 * k``（``rw`` 代表 "rewrite"），
而 ``ring`` 策略则解决了得到的目标 ``m * (2 * k) = 2 * (m * k)``。

以小步骤构建证明并伴随增量反馈的能力
是非常强大的。因此，
策略证明通常比证明项更容易、更快速地编写。
两者之间并没有严格的区别：
策略证明可以插入到证明项中，
就像我们在上面的例子中使用 ``by rw [hk, mul_add]`` 短语那样。
我们还将看到，反过来，
在策略证明中插入一个简短的证明项往往也很有用。
尽管如此，在本书中，我们的重点将放在策略的使用上。

在我们的例子中，策略证明也可以简化为一行：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring
-- QUOTE.

/- TEXT:
这里我们使用策略进行了一些小的证明步骤。
但它们也可以提供大量的自动化，
并支持更长的计算和更大的推理步骤。
例如，我们可以调用 Lean 的简化器，
用特定的规则来简化关于奇偶性的陈述，
从而自动证明我们的定理。
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
-- QUOTE.

/- TEXT:
两个介绍之间的另一个重大区别是，
*Theorem Proving in Lean* 仅依赖核心 Lean 及其内置策略，
而 *Mathematics in Lean* 建立在 Lean 强大且不断增长的库 *Mathlib* 之上。
因此，我们可以向你展示如何使用库中的一些数学对象和定理，
以及一些非常有用的策略。
本书并非旨在作为库的完整概述；
`社区 <https://leanprover-community.github.io/>`_
网页包含了详尽的文档。
相反，我们的目标是向你介绍形式化背后的思维方式，
并指出基本的入口点，
以便你能够轻松浏览库并自行找到所需内容。

交互式定理证明可能会令人沮丧，
学习曲线也很陡峭。
但 Lean 社区对新来者非常友好，
在
`Lean Zulip 聊天群组 <https://leanprover.zulipchat.com/>`_
上随时都有人回答问题。
我们希望在那里见到你，并且毫不怀疑
很快你也能回答这些问题
并为 *Mathlib* 的发展做出贡献。

那么，如果你选择接受的话，这是你的任务：
投入其中，尝试练习，有问题就来 Zulip 提问，享受乐趣。
但需要预先警告：
交互式定理证明将挑战你以全新的方式
思考数学和数学推理。
你的生活可能会因此而改变。

*致谢。* 我们感谢 Gabriel Ebner 为在 VS Code 中
运行本教程搭建的基础设施，
以及 Kim Morrison 和 Mario Carneiro 帮助将其从 Lean 4 移植过来。
我们还感谢以下人士的帮助和修正：
Takeshi Abe、
Julian Berman、Alex Best、Thomas Browning、
Bulwi Cha、Hanson Char、Bryan Gin-ge Chen、Steven Clontz、Mauricio Collaris、Johan Commelin、
Mark Czubin、
Alexandru Duca、
Pierpaolo Frasa、
Denis Gorbachev、Winston de Greef、Mathieu Guay-Paquet、
Marc Huisinga、
Benjamin Jones、
Julian Külshammer、
Victor Liu、Jimmy Lu、
Martin C. Martin、Giovanni Mascellani、John McDowell、Joseph McKinsey、Bhavik Mehta、Isaiah Mindich、
Kabelo Moiloa、Hunter Monroe、Pietro Monticone、
Oliver Nash、Emanuelle Natale、Filippo A. E. Nuccio、
Pim Otte、
Bartosz Piotrowski、
Nicolas Rolland、Keith Rush、
Yannick Seurin、Guilherme Silva、Bernardo Subercaseaux、
Pedro Sánchez Terraf、Matthew Toohey、Alistair Tucker、
Floris van Doorn、
Eric Wieser、
以及其他人。
我们的工作得到了 Hoskinson Center for Formal Mathematics 的部分资助。
TEXT. -/
