import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

/- TEXT:
.. _disjunction:

析取
-----------

.. index:: left, right, tactics ; left, tactics ; right

证明析取 ``A ∨ B`` 的规范方法是证明
``A`` 或证明 ``B``。
``left`` 策略选择 ``A``，
``right`` 策略选择 ``B``。
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {x y : ℝ}

-- EXAMPLES:
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]
-- QUOTE.

/- TEXT:
我们不能使用匿名构造子来构造
一个“或”的证明，因为 Lean 将不得不猜测
我们试图证明哪个析取支。
在编写证明项时，我们可以
使用 ``Or.inl`` 和 ``Or.inr``
来显式地做出选择。
这里 ``inl`` 是 "introduction left"（左引入）的缩写，
``inr`` 是 "introduction right"（右引入）的缩写。
TEXT. -/
-- QUOTE:
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h
-- QUOTE.

/- TEXT:
通过证明某一边来证明一个析取命题，可能看起来很奇怪。
在实践中，哪个情况成立通常取决于假设和数据中
隐含或显式的分类讨论。
``rcases`` 策略允许我们使用
形如 ``A ∨ B`` 的假设。
与对合取或存在量词使用 ``rcases`` 不同，
这里的 ``rcases`` 策略产生*两个*目标。
两者有相同的结论，但在第一种情况下，
``A`` 被假定为真，
而在第二种情况下，
``B`` 被假定为真。
换句话说，顾名思义，
``rcases`` 策略执行的是分情况证明。
和往常一样，我们可以告诉 Lean 使用什么名称来命名假设。
在下一个例子中，我们告诉 Lean
在每个分支中使用名称 ``h``。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- TEXT:
注意模式从合取情况下的 ``⟨h₀, h₁⟩`` 变为
析取情况下的 ``h₀ | h₁``。
将第一种模式理解为匹配同时包含
``h₀`` 和 ``h₁`` 的数据，而第二种模式，带有竖线，
理解为匹配包含 ``h₀`` *或* ``h₁`` 的数据。
在这里，因为两个目标是分开的，我们选择
在每种情况下使用相同的名称 ``h``。

绝对值函数被定义为
我们可以立即证明
``x ≥ 0`` 蕴含 ``|x| = x``
（这是定理 ``abs_of_nonneg``）
以及 ``x < 0`` 蕴含 ``|x| = -x``（这是 ``abs_of_neg``）。
表达式 ``le_or_gt 0 x`` 建立了 ``0 ≤ x ∨ x < 0``，
允许我们在这两种情况下分情况讨论。

Lean 也支持计算机科学家的模式匹配
语法来处理析取。现在 ``cases`` 策略更有吸引力了，
因为它允许我们命名每个 ``case``，并命名更靠近
使用位置的被引入的假设。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- TEXT:
名称 ``inl`` 和 ``inr`` 分别是 "intro left"（左引入）和 "intro right"（右引入）的缩写。
使用 ``case`` 的优点是你可以按任意顺序证明
各种情况；Lean 使用标签来找到相关的目标。
如果你不关心这一点，你可以使用 ``next``、``match``，
甚至是模式匹配的 ``have``。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h
-- QUOTE.

/- TEXT:
在 ``match`` 的情况下，我们需要使用证明析取的
规范方式的全名 ``Or.inl`` 和 ``Or.inr``。
在本教材中，我们通常使用 ``rcases`` 来对
析取的各种情况进行分类讨论。

尝试使用下一个片段中的
前两个定理来证明三角不等式。
它们被赋予与 Mathlib 中相同的名称。
TEXT. -/
-- BOTH:
-- QUOTE:
namespace MyAbs

-- EXAMPLES:
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem le_abs_selfαα (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_selfαα (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add_leαα (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

/- TEXT:
如果你喜欢这些（双关语是故意的——pun intended），并且
想要更多关于析取的练习，
试试这些。
TEXT. -/
-- QUOTE:
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem lt_absαα : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith
    · exact h'

theorem abs_ltαα : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    · intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

-- BOTH:
end MyAbs

end

/- TEXT:
你也可以使用 ``rcases`` 和 ``rintro`` 处理嵌套析取。
当这些导致真正的分情况讨论且产生多个目标时，
每个新目标的模式用竖线分隔。
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt
-- QUOTE.

/- TEXT:
你仍然可以嵌套模式并使用 ``rfl`` 关键字
来代入等式：
TEXT. -/
-- QUOTE:
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right
-- QUOTE.

/- TEXT:
看看你能否用单行（长行）证明以下命题。
使用 ``rcases`` 来解包假设并对情况分类讨论，
并使用 ``<;> linarith`` 来解决每个分支。
TEXT. -/
-- QUOTE:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

/- TEXT:
在实数上，等式 ``x * y = 0``
告诉我们 ``x = 0`` 或 ``y = 0``。
在 Mathlib 中，这个事实被称为 ``eq_zero_or_eq_zero_of_mul_eq_zero``，
它是析取如何产生的另一个很好的例子。
看看你能否使用它来证明以下命题：
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

/- TEXT:
记住你可以使用 ``ring`` 策略来帮助
进行计算。

在任意环 :math:`R` 中，一个元素 :math:`x` 如果
对某个非零 :math:`y` 满足 :math:`x y = 0`，则称为
*左零因子*；
一个元素 :math:`x` 如果
对某个非零 :math:`y` 满足 :math:`y x = 0`，则称为
*右零因子*；
而一个元素如果是左零因子或右零因子，
则简称为*零因子*。
定理 ``eq_zero_or_eq_zero_of_mul_eq_zero``
说明实数没有非平凡的零因子。
具有此性质的交换环称为*整环*。
你上面两个定理的证明在任何整环中
都应该同样有效：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

-- EXAMPLES:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

-- BOTH:
end

/- TEXT:
事实上，如果你小心的话，你可以无需使用乘法交换律
来证明第一个
定理。在这种情况下，假设 ``R`` 是
``Ring`` 而不是 ``CommRing`` 就足够了。

.. index:: excluded middle

有时在证明中我们想要根据某个命题是否成立
来分情况讨论。
对于任何命题 ``P``，我们可以使用
``em P : P ∨ ¬ P``。
名称 ``em`` 是 "excluded middle"（排中律）的缩写。
TEXT. -/
-- QUOTE:
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction
-- QUOTE.

/- TEXT:
.. index:: by_cases, tactics ; by_cases

或者，你可以使用 ``by_cases`` 策略。

TEXT. -/
-- QUOTE:
-- EXAMPLES:
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction
-- QUOTE.

/- TEXT:
注意 ``by_cases`` 策略允许你
为在每个分支中引入的假设指定一个标签，
这里是 ``h' : P`` 在一个分支中，``h' : ¬ P``
在另一个分支中。
如果你省略标签，
Lean 默认使用 ``h``。
尝试证明以下等价关系，
使用 ``by_cases`` 来建立一个方向。
TEXT. -/
-- QUOTE:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h
