-- BOTH:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

/- TEXT:
.. _using_theorems_and_lemmas:

使用定理和引理
-------------------------

.. index:: inequalities

重写对于证明等式来说非常有用，
但其他类型的定理呢？
例如，我们如何证明一个不等式，
比如 :math:`a + e^b \le a + e^c` 在 :math:`b \le c` 时成立这个事实？
我们已经看到定理可以应用于参数和假设，
并且 ``apply`` 和 ``exact`` 策略可以用来解决目标。
在本节中，我们将充分利用这些工具。

考虑库定理 ``le_refl`` 和 ``le_trans``：
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- QUOTE.

/- TEXT:
正如我们在 :numref:`implication_and_the_universal_quantifier` 中详细解释的那样，
``le_trans`` 陈述中的隐式括号
是向右结合的，因此它应该被解释为 ``a ≤ b → (b ≤ c → a ≤ c)``。
库设计者将 ``le_trans`` 的参数 ``a``、``b`` 和 ``c`` 设置为隐式的，
这样 Lean *不会* 让你显式地提供它们（除非你
真的坚持，我们将在后面讨论）。
相反，它期望从使用它们的上下文中推断它们。
例如，当假设 ``h : a ≤ b`` 和 ``h' : b ≤ c``
在上下文中时，
以下所有方式都有效：
TEXT. -/
section
-- QUOTE:
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
-- QUOTE.

end

/- TEXT:
.. index:: apply, tactics ; apply, exact, tactics ; exact

``apply`` 策略接受一个一般陈述或蕴含式的证明，
尝试将结论与当前目标匹配，
并将假设（如果有的话）留作新目标。
如果给定的证明与目标完全匹配
（模 *定义* 相等），
你可以使用 ``exact`` 策略代替 ``apply``。
因此，所有这些都有效：
TEXT. -/
-- QUOTE:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
-- QUOTE.

/- TEXT:
在第一个例子中，应用 ``le_trans``
创建了两个目标，
我们使用点号来指示每个目标的证明从哪里开始。
点号是可选的，但它们用于 *聚焦* 目标：
在点号引入的块内，只有一个目标是可见的，
并且必须在块结束之前完成。
这里我们通过用另一个点号开始一个新块来结束第一个块。
我们同样可以减小缩进。
在第三个例子和最后一个例子中，
我们完全避免了进入策略模式：
``le_trans h₀ h₁`` 和 ``le_refl x`` 是我们需要的证明项。

这里还有一些库定理：
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- QUOTE.

/- TEXT:
结合 ``apply`` 和 ``exact`` 使用它们来证明以下内容：
TEXT. -/
-- 尝试这个。
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

/- TEXT:
.. index:: linarith, tactics ; linarith

事实上，Lean 有一个策略可以自动完成这类事情：
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- QUOTE.

/- TEXT:
``linarith`` 策略旨在处理 *线性算术*。
TEXT. -/
section

-- QUOTE:
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
-- QUOTE.

end

/- TEXT:
除了上下文中的等式和不等式之外，
``linarith`` 还会使用你作为参数传递的额外不等式。
在下一个例子中，``exp_le_exp.mpr h'`` 是
``exp b ≤ exp c`` 的证明，我们稍后会解释。
注意，在 Lean 中，我们用 ``f x`` 来表示
函数 ``f`` 应用于参数 ``x``，
与我们写 ``h x`` 来表示
事实或定理 ``h`` 应用于参数 ``x`` 的结果完全相同。
括号仅对复合参数是必需的，
如 ``f (x + y)``。没有括号时，``f x + y``
会被解析为 ``(f x) + y``。
TEXT. -/
-- QUOTE:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
-- QUOTE.

/- TEXT:
.. index:: exponential, logarithm

这里是库中的一些可用于建立实数上不等式的定理。
TEXT. -/
-- QUOTE:
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right
-- QUOTE.

/- TEXT:
其中一些定理，如 ``exp_le_exp``、``exp_lt_exp``
使用 *双向蕴含*，它表示
"当且仅当"。
（你可以在 VS Code 中用 ``\lr`` 或 ``\iff`` 输入它）。
我们将在下一章更详细地讨论这个连接词。
这样的定理可以与 ``rw`` 一起使用，将目标重写为
一个等价的目标：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
-- QUOTE.

/- TEXT:
然而，在本节中，我们将使用这样一个事实：如果 ``h : A ↔ B``
是这样的等价关系，
那么 ``h.mp`` 建立了正向，``A → B``，
而 ``h.mpr`` 建立了反向，``B → A``。
这里，``mp`` 代表"肯定前件"，
``mpr`` 代表"肯定前件逆向"。
如果你喜欢，也可以用 ``h.1`` 和 ``h.2`` 分别表示 ``h.mp`` 和 ``h.mpr``。
因此下面的证明有效：
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-- QUOTE.

/- TEXT:
第一行 ``apply add_lt_add_of_lt_of_le``
创建了两个目标，
我们再次使用点号来分隔
第一个的证明和第二个的证明。

.. index:: norm_num, tactics ; norm_num

尝试自己完成以下示例。
中间的示例向你展示了 ``norm_num``
策略可以用来解决具体的数值目标。
TEXT. -/
-- QUOTE:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  apply log_le_log h₀
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_right
  rw [exp_le_exp]
  apply add_le_add_right h₀

-- 使用 `linarith` 的替代方案。
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  apply log_le_log h₀
  apply add_le_add_right (exp_le_exp.mpr h)

-- 解答。
/- TEXT:
从这些示例中应该清楚，能够找到
你需要的库定理是形式化的重要组成部分。
你可以使用多种策略：

* 你可以在 Mathlib 的
  `GitHub 仓库 <https://github.com/leanprover-community/mathlib4>`_ 中浏览。

* 你可以使用 Mathlib
  `网页 <https://leanprover-community.github.io/mathlib4_docs/>`_ 上的 API 文档。

* 你可以使用 `Loogle <https://loogle.lean-lang.org>`_
  按模式搜索 Lean 和 Mathlib 的定义和定理。

* 你可以依赖 Mathlib 的命名约定和编辑器中的 Ctrl-空格补全
  来猜测定理名称（Mac 键盘上是 Cmd-空格）。
  在 Lean 中，名为 ``A_of_B_of_C`` 的定理
  从形如 ``B`` 和 ``C`` 的假设中建立形如 ``A`` 的结论，
  其中 ``A``、``B`` 和 ``C``
  大致对应于我们大声读出目标的方式。
  因此，一个建立类似于 ``x + y ≤ ...`` 的定理
  可能以 ``add_le`` 开头。
  输入 ``add_le`` 并按 Ctrl-空格会给你一些有用的选择。
  注意，按两次 Ctrl-空格会显示关于可用补全的更多信息。

* 如果你在 VS Code 中右键单击一个现有的定理名称，
  编辑器会显示一个菜单，其中包含
  跳转到定义该定理的文件的选项，
  你可以在附近找到类似的定理。

* 你可以使用 ``apply?`` 策略，
  它会尝试在库中找到相关的定理。
TEXT. -/
-- QUOTE:
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
-- QUOTE.

/- TEXT:
要在这个例子中尝试 ``apply?``，
删除 ``exact`` 命令并取消注释上一行。
使用这些技巧，
看看你能否找到完成下一个示例所需的东西：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  exact exp_le_exp.mpr h

-- 替代方案：
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  linarith [exp_le_exp.mpr h]

/- TEXT:
使用相同的技巧，确认 ``linarith`` 而不是 ``apply?``
也可以完成这项工作。

这里是另一个不等式的例子：
TEXT. -/
-- QUOTE:
example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring
-- QUOTE.

/- TEXT:
Mathlib 倾向于在二元运算符如 ``*`` 和 ``^`` 周围加空格，
但在这个例子中，更紧凑的格式增加了可读性。
有几个值得注意的地方。
首先，表达式 ``s ≥ t`` 在定义上等价于 ``t ≤ s``。
原则上，这意味着二者应该可以互换使用。
但 Lean 的一些自动化不识别这种等价性，
因此 Mathlib 倾向于使用 ``≤`` 而非 ``≥``。
其次，我们广泛使用了 ``ring`` 策略。
它真的是一个节省时间的工具！
最后，注意在第二个 ``calc`` 证明的第二行中，
我们可以简单地写入证明项 ``add_le_add (le_refl _) h``，
而不是写 ``by exact add_le_add (le_refl _) h``。

事实上，上述证明中唯一巧妙的地方是找出
假设 ``h``。
一旦我们有了它，第二个计算只涉及
线性算术，``linarith`` 可以处理它：
TEXT. -/
-- QUOTE:
example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
-- QUOTE.

/- TEXT:
多好啊！我们挑战你使用这些想法来证明
以下定理。你可以使用定理 ``abs_le'.mpr``。
你还需要 ``constructor`` 策略将一个合取式
拆分为两个目标；参见 :numref:`conjunction_and_biimplication`。
TEXT. -/
-- QUOTE:
example : |a*b| ≤ (a^2 + b^2)/2 := by
  sorry

#check abs_le'.mpr
-- QUOTE.

-- SOLUTIONS:
theorem fact1 : a*b*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a*b)*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 + 2*a*b + b^2
  calc
    a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff₀ h]
    apply fact1
  rw [le_div_iff₀ h]
  apply fact2

/- TEXT:
如果你成功解决了这个问题，恭喜你！
你正在成为一位形式化大师的道路上稳步前进。
TEXT. -/
