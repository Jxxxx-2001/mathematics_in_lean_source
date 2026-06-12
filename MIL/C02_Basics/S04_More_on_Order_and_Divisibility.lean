-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

/- TEXT:
.. _more_on_order_and_divisibility:

更多使用 apply 和 rw 的例子
--------------------------------

.. index:: min, max

实数上的 ``min`` 函数由以下三个事实
唯一刻画：
TEXT. -/
-- BOTH:
section
variable (a b c d : ℝ)

-- QUOTE:
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- QUOTE.

/- TEXT:
你能猜出以类似方式刻画
``max`` 的定理名称吗？

注意，我们必须通过写 ``min a b`` 而不是 ``min (a, b)``
将 ``min`` 应用于一对参数 ``a`` 和 ``b``。
形式上，``min`` 是一个类型为 ``ℝ → ℝ → ℝ`` 的函数。
当我们写像这样带有多个箭头的类型时，
惯例是隐式括号向右结合，
因此该类型被解释为 ``ℝ → (ℝ → ℝ)``。
最终效果是，如果 ``a`` 和 ``b`` 的类型是 ``ℝ``，
那么 ``min a`` 的类型是 ``ℝ → ℝ``，
而 ``min a b`` 的类型是 ``ℝ``，因此 ``min`` 像一个
两个参数的函数一样运作，正如我们所期望的。以这种方式处理多个
参数被称为 *柯里化*，
以逻辑学家 Haskell Curry 命名。

Lean 中运算的顺序也可能需要一些时间来适应。
函数应用比中缀运算绑定得更紧，因此
表达式 ``min a b + c`` 被解释为 ``(min a b) + c``。
随着时间推移，这些约定将成为你的第二本能。

使用定理 ``le_antisymm``，我们可以证明两个
实数相等，如果每个都小于等于另一个。
利用这一点以及上述事实，
我们可以证明 ``min`` 是可交换的：
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
-- QUOTE.

/- TEXT:
.. index:: show, tactics ; show

这里我们使用了点号来分隔
不同目标的证明。
我们的用法不一致：
在外层级别，
我们对两个目标都使用点号和缩进，
而对于嵌套的证明，
我们只使用点号直到只剩下一个目标。
两种约定都是合理的且有用的。
我们还使用 ``show`` 策略来结构化
证明
并指示每个块中要证明什么。
没有 ``show`` 命令，证明仍然有效，
但使用它们使证明更易于阅读和维护。

可能会让你烦恼的是这个证明是重复的。
为了预示你以后将学到的技能，
我们注意到避免重复的一种方法是
陈述一个局部引理然后使用它：
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
-- QUOTE.

/- TEXT:
我们将在
:numref:`implication_and_the_universal_quantifier` 中更多地讨论全称量词，
但在这里只需说明假设
``h`` 表明所需的不等式对
任意 ``x`` 和 ``y`` 都成立，
而 ``intro`` 策略引入任意的
``x`` 和 ``y`` 来建立结论。
``le_antisymm`` 之后的第一个 ``apply`` 隐式地
使用 ``h a b``，而第二个使用 ``h b a``。

.. index:: repeat, tactics ; repeat

另一种解决方案是使用 ``repeat`` 策略，
它尽可能多次地
应用一个策略（或一个块）。
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
-- QUOTE.

/- TEXT:
我们鼓励你将以下内容作为练习来证明。
你可以使用刚才描述的任何一种技巧来缩短第一个。
TEXT. -/
-- QUOTE:
-- BOTH:
example : max a b = max b a := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- BOTH:
example : min (min a b) c = min a (min b c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right
-- QUOTE.

/- TEXT:
当然，欢迎你也证明 ``max`` 的结合律。

一个有趣的事实是，``min`` 对 ``max`` 满足分配律，
就像乘法对加法满足分配律一样，
反之亦然。
换句话说，在实数上，我们有恒等式
``min a (max b c) = max (min a b) (min a c)``
以及相应的 ``max`` 和 ``min``
交换的版本。
但在下一节中我们将看到，这 *不* 能从
``≤`` 的传递性和自反性以及
上面列举的 ``min`` 和 ``max`` 的刻画性质
推导出来。
我们需要使用这样一个事实：实数上的 ``≤`` 是一个 *全序*，
也就是说，
它满足 ``∀ x y, x ≤ y ∨ y ≤ x``。
这里析取符号 ``∨`` 表示"或"。
在第一种情况下，我们有 ``min x y = x``，
在第二种情况下，我们有 ``min x y = y``。
我们将在 :numref:`disjunction` 中学习如何按情况推理，
但目前我们只关注不需要分情况的例子。

这里是这样一个例子：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_min
  · apply add_le_add_left
    apply min_le_left
  apply add_le_add_left
  apply min_le_right

-- BOTH:
example : min a b + c = min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_left
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]
-- QUOTE.

/- TEXT:
很明显，``aux`` 提供了证明等式所需的两个不等式之一，
但将其应用于适当的值同样可以得到另一个方向。
作为提示，你可以使用定理 ``add_neg_cancel_right``
和 ``linarith`` 策略。

.. index:: absolute value

Lean 的命名约定在库中三角不等式的
名称中体现得很明显：
TEXT. -/
-- QUOTE:
#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
-- QUOTE.

/- TEXT:
使用它来证明以下变体，同时使用 ``add_sub_cancel_right``：
TEXT. -/
-- QUOTE:
-- BOTH:
example : |a| - |b| ≤ |a - b| :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add_le
    _ ≤ |a - b| := by rw [add_sub_cancel_right]


-- 替代方案
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b
  rw [sub_add_cancel] at h
  linarith

-- BOTH:
end
-- QUOTE.

/- TEXT:
看看你能否在三行或更少的行数内完成。
你可以使用定理 ``sub_add_cancel``。

.. index:: divisibility

我们在接下来的章节中会使用到的
另一个重要关系是自然数上的整除关系，
``x ∣ y``。
注意：整除符号 *不是*
你键盘上的普通竖线。
相反，它是一个 Unicode 字符，通过在 VS Code 中
输入 ``\|`` 来获得。
按照约定，Mathlib 在定理名称中使用 ``dvd``
来指代它。
TEXT. -/
-- BOTH:
section
variable (w x y z : ℕ)

-- QUOTE:
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left
-- QUOTE.

/- TEXT:
在最后一个例子中，指数是一个自然
数，应用 ``dvd_mul_left``
会迫使 Lean 将 ``x^2`` 展开为
``x^1 * x``。
看看你能否猜出证明以下内容
所需的定理名称：
TEXT. -/
-- QUOTE:
-- BOTH:
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

-- BOTH:
end
-- QUOTE.

/- TEXT:
.. index:: gcd, lcm

关于整除关系，*最大公约数*，
``gcd``，和最小公倍数，``lcm``，
类似于 ``min`` 和 ``max``。
由于每个数都整除 ``0``，
``0`` 实际上是整除关系下的最大元素：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
-- QUOTE.

/- TEXT:
看看你能否猜出证明以下内容所需的定理名称：
TEXT. -/
-- QUOTE:
-- BOTH:
example : Nat.gcd m n = Nat.gcd n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
-- QUOTE.

-- BOTH:
end

/- TEXT:
提示：你可以使用 ``dvd_antisymm``，但如果你这样做，Lean 会
抱怨该表达式在通用定理和版本 ``Nat.dvd_antisymm``
（专门用于自然数的版本）之间是模糊的。
你可以使用 ``_root_.dvd_antisymm`` 来指定通用版本；
两者都可以使用。
TEXT. -/

-- OMIT: fix this: protect `dvd_antisymm`.
