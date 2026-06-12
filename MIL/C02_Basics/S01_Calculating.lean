import MIL.Common
import Mathlib.Data.Real.Basic
/- TEXT:
计算
--------

我们通常学习进行数学计算时，
并不把它们当作证明来看待。
但当我们对计算中的每一步进行论证时，
正如 Lean 要求我们做的那样，
最终的结果就是一个证明，表明计算的左边
等于右边。

.. index:: rewrite, rw, tactics ; rw and rewrite

在 Lean 中，陈述一个定理等同于陈述一个目标，
即证明该定理的目标。
Lean 提供了重写策略 ``rw``，
用于将目标中等式左边替换为右边。
如果 ``a``、``b`` 和 ``c`` 是实数，
则 ``mul_assoc a b c`` 是恒等式 ``a * b * c = a * (b * c)``，
而 ``mul_comm a b`` 是恒等式 ``a * b = b * a``。
Lean 提供的自动化通常可以避免
显式引用这些事实的需要，
但它们在举例说明时很有用。
在 Lean 中，乘法是左结合的，
因此 ``mul_assoc`` 的左边也可以写成 ``(a * b) * c``。
然而，一般来说，注意 Lean 的记号约定、
在 Lean 省略括号的地方也省略括号，是良好的风格。

让我们尝试使用 ``rw``。

.. index:: real numbers
TEXT. -/
-- 一个例子。
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
-- QUOTE.

/- TEXT:
相关示例文件开头的 ``import`` 行
从 Mathlib 导入了实数理论以及有用的自动化工具。
为了简洁起见，
我们在教材中通常省略这些信息。

欢迎你进行修改来看看会发生什么。
你可以在 VS Code 中输入 ``\R`` 或 ``\real``
来输入 ``ℝ`` 字符。
直到你按下空格键或 Tab 键后，该符号才会出现。
如果在阅读 Lean 文件时将鼠标悬停在某个符号上，
VS Code 会显示用于输入该符号的语法。
如果你好奇想查看所有可用的缩写，可以按 Ctrl-Shift-P，
然后输入 abbreviations 来访问 ``Lean 4: Show Unicode Input Abbreviations`` 命令。
如果你的键盘没有容易按到的反斜杠键，
可以通过更改 ``lean4.input.leader`` 设置
来更改引导字符。

.. index:: proof state, local context, goal

当光标位于策略证明的中间时，
Lean 会在 *Lean 信息视图* 窗口中
报告当前的 *证明状态*。
当你在证明的每一步移动光标时，
你可以看到状态的变化。
Lean 中典型的证明状态可能如下所示：

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

以 ``⊢`` 开头的行之前的行表示 *上下文*：
它们是当前涉及的对象和假设。
在这个例子中，包括两个对象 ``x`` 和 ``y``，
每个都是自然数。
还包括三个假设，
标记为 ``h₁``、``h₂`` 和 ``h₃``。
在 Lean 中，上下文中的每个对象都有一个标识符标签。
你可以通过输入 ``h\1``、``h\2`` 和 ``h\3`` 来输入这些带下标的标签，
但任何合法的标识符都可以：
你可以使用 ``h1``、``h2``、``h3``，
或者 ``foo``、``bar`` 和 ``baz``。
最后一行表示 *目标*，
即需要证明的事实。
有时人们用 *target* 指代需要证明的事实，
而用 *goal* 指代上下文和目标的组合。
在实践中，其含义通常从上下文就能看清。

尝试证明这些恒等式，
在每个例子中用策略证明替换 ``sorry``。
使用 ``rw`` 策略时，你可以用左箭头（``\l``）
来反向使用一个恒等式。
例如，``rw [← mul_assoc a b c]``
在当前目标中将 ``a * (b * c)`` 替换为 ``a * b * c``。注意，
左箭头指的是在 ``mul_assoc`` 提供的恒等式中从右边到左边，
这与目标的左边或右边无关。
TEXT. -/
-- 尝试这些。
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/- TEXT:
你也可以在不提供参数的情况下使用 ``mul_assoc`` 和 ``mul_comm`` 等恒等式。
在这种情况下，重写策略会尝试将左边与
目标中的表达式匹配，
使用它找到的第一个模式。
TEXT. -/
-- 一个例子。
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- TEXT:
你也可以提供 *部分* 信息。
例如，``mul_comm a`` 匹配任何形如
``a * ?`` 的模式，并将其重写为 ``? * a``。
尝试对第一个例子完全不提供参数，
对第二个例子只提供一个参数。
TEXT. -/
/- 尝试对第一个例子完全不提供参数，对第二个例子只提供一个参数。 -/
-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- TEXT:
你也可以在 ``rw`` 中使用来自局部上下文的事实。
TEXT. -/
-- 使用来自局部上下文的事实。
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.

/- TEXT:
尝试这些，对第二个使用定理 ``sub_self``：
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

/- TEXT:
多个重写命令可以通过一个命令执行，
只需在方括号内用逗号分隔列出相关的恒等式即可。
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

/- TEXT:
你可以通过将光标放在任何重写列表中的逗号后面
来逐步观察证明进展。

另一个技巧是，我们可以一次性在示例或定理之外
声明变量。然后 Lean 会自动包含它们。
TEXT. -/
section

-- QUOTE:
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

end

/- TEXT:
查看上述证明开始时的策略状态
会显示 Lean 确实包含了所有变量。
我们可以通过将声明放在
``section ... end`` 块中来界定其作用域。
最后，回顾引言中所述，Lean 为我们提供了一个
确定表达式类型的命令：
TEXT. -/
-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.

/- TEXT:
``#check`` 命令既适用于对象，也适用于事实。
在响应命令 ``#check a`` 时，Lean 报告 ``a`` 的类型是 ``ℝ``。
在响应命令 ``#check mul_comm a b`` 时，
Lean 报告 ``mul_comm a b`` 是事实 ``a * b = b * a`` 的证明。
命令 ``#check (a : ℝ)`` 申明我们期望
``a`` 的类型是 ``ℝ``，
如果不是这样，Lean 会报错。
我们稍后会解释最后三个 ``#check`` 命令的输出，
但与此同时，你可以看看它们，
并自己尝试一些 ``#check`` 命令。

让我们再试一些例子。定理 ``two_mul a`` 表示
``2 * a = a + a``。定理 ``add_mul`` 和 ``mul_add``
表达了乘法对加法的分配律，
而定理 ``add_assoc`` 表达了加法的结合律。
使用 ``#check`` 命令来查看精确的陈述。

.. index:: calc, tactics ; calc
TEXT. -/
section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
虽然可以通过在编辑器中逐步执行来理解这个证明的过程，
但单独阅读它很难理解。
Lean 提供了一种更结构化的方式来编写这样的证明，
即使用 ``calc`` 关键字。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
注意，该证明 *不* 以 ``by`` 开头：
以 ``calc`` 开头的表达式是一个 *证明项*。
``calc`` 表达式也可以在策略证明内部使用，
但 Lean 将其解释为使用生成的
证明项来解决目标。
``calc`` 语法很讲究：下划线和理由
必须以上述格式呈现。
Lean 利用缩进来确定诸如策略块或 ``calc`` 块
从哪里开始和结束；
尝试更改上述证明中的缩进，看看会发生什么。

编写 ``calc`` 证明的一种方法是先使用
``sorry`` 策略作为理由勾勒出框架，
确保 Lean 接受忽略这些抱歉后的表达式，
然后再用策略来证明各个步骤。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.

end

/- TEXT:
尝试使用纯 ``rw`` 证明和更结构化的 ``calc`` 证明
来证明以下恒等式：
TEXT. -/
-- 尝试这些。对于第二个，使用下面列出的定理。
section
variable (a b c d : ℝ)

-- QUOTE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- QUOTE.

/- TEXT:
下面的练习稍微更有挑战性一些。
你可以使用下面列出的定理。
TEXT. -/
-- QUOTE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- QUOTE.

end

/- TEXT:
.. index:: rw, tactics ; rw and rewrite

我们也可以在上下文中的假设里进行重写。
例如，``rw [mul_comm a b] at hyp`` 将假设 ``hyp`` 中的
``a * b`` 替换为 ``b * a``。
TEXT. -/
-- 示例。

section
variable (a b c d : ℝ)

-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-- QUOTE.

/- TEXT:
.. index:: exact, tactics ; exact

在最后一步中，``exact`` 策略可以使用 ``hyp`` 来解决目标，
因为此时 ``hyp`` 与目标完全匹配。

.. index:: ring (tactic), tactics ; ring

在本节结束时，我们注意到 Mathlib 提供了一个
非常有用的自动化工具 ``ring`` 策略，
它旨在证明任何交换环中的恒等式，只要它们完全由环公理推导出来，
而不使用任何局部假设。
TEXT. -/
-- QUOTE:
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
``ring`` 策略在我们导入
``Mathlib.Data.Real.Basic`` 时间接被导入，
但我们将在下一节中看到，它可以用于
实数以外的其他结构上的计算。
它可以通过命令 ``import Mathlib.Tactic`` 显式导入。
我们将看到，对于其他常见类型的代数结构，
也有类似的策略。

``rw`` 有一个变体叫做 ``nth_rw``，它允许你只替换目标中表达式的特定实例。
可能的匹配从 1 开始编号，
因此在下面的例子中，``nth_rw 2 [h]`` 将第二个
出现的 ``a + b`` 替换为 ``c``。
EXAMPLES: -/
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
-- QUOTE.
