-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

/- TEXT:
.. _conjunction_and_biimplication:

合取与当且仅当
-------------------

.. index:: constructor, tactics ; constructor

你已经看到合取符号 ``∧``
用于表示“且”。
``constructor`` 策略允许你通过先证明 ``A``
再证明 ``B`` 来证明
形如 ``A ∧ B`` 的命题。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
-- QUOTE.

/- TEXT:
.. index:: assumption, tactics ; assumption

在这个例子中，``assumption`` 策略
告诉 Lean 寻找一个能解决目标的假设。
注意最后的 ``rw`` 通过
应用 ``≤`` 的自反性完成了目标。
以下是使用匿名构造子尖括号
完成前面例子的几种替代方式。
第一个是前一个证明
的简洁证明项版本，
它在关键字 ``by`` 处进入策略模式。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩
-- QUOTE.

/- TEXT:
*使用*一个合取而非证明一个合取涉及解包其
两个部分的证明。
你可以使用 ``rcases`` 策略来做到这一点，
以及 ``rintro`` 或模式匹配的 ``fun``，
所有这些都以类似于它们用于
存在量词的方式使用。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- TEXT:
与 ``obtain`` 策略类似，也有模式匹配的 ``have``：
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
-- QUOTE.

/- TEXT:
与 ``rcases`` 不同，这里的 ``have`` 策略将 ``h`` 保留在上下文中。
尽管我们不会使用它们，但我们再次看到了计算机科学家的
模式匹配语法：
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁
-- QUOTE.

/- TEXT:
与使用存在量词不同，
你也可以通过写 ``h.left`` 和 ``h.right``，
或等价地 ``h.1`` 和 ``h.2``，
来提取假设 ``h : A ∧ B`` 中
两个分量的证明。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
-- QUOTE.

/- TEXT:
尝试使用这些技巧来想出证明以下命题的各种方式：
TEXT. -/
-- QUOTE:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply Nat.dvd_antisymm h0 h2

/- TEXT:
你可以嵌套使用 ``∃`` 和 ``∧``，
配合匿名构造子、``rintro`` 和 ``rcases``。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_z, xltz, zlty⟩ ↦ lt_trans xltz zlty
-- QUOTE.

/- TEXT:
回忆一下，在 `z` 前面加下划线告诉 Lean 我们不打算使用 `z`。
否则 Lean 会输出一个警告说 `z` 未被使用。

你也可以使用 ``use`` 策略：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- TEXT:
在第一个例子中，``constructor`` 命令后面的 ``<;>`` 告诉 Lean 对
产生的两个目标都使用 ``norm_num`` 策略。

在 Lean 中，``A ↔ B`` *不*被定义为 ``(A → B) ∧ (B → A)``，
但它本来可以这样定义，
而且它的行为大致相同。
你已经看到，对于 ``h : A ↔ B``，
你可以写 ``h.mp`` 和 ``h.mpr``
或 ``h.1`` 和 ``h.2`` 来获取两个方向。
你也可以使用 ``cases`` 及类似命令。
要证明一个当且仅当命题，
你可以使用 ``constructor`` 或尖括号，
就像证明合取一样。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
-- QUOTE.

/- TEXT:
最后一个证明项难以理解。记住你可以在编写
这样的表达式时使用下划线来
查看 Lean 期望什么。

尝试使用你刚刚看到的各种技巧和工具
来证明以下命题：
TEXT. -/
-- QUOTE:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

/- TEXT:
一个更有趣的练习是，对于任意
两个实数 ``x`` 和 ``y``，
证明 ``x^2 + y^2 = 0`` 当且仅当 ``x = 0`` 且 ``y = 0``。
我们建议使用
``linarith``、``pow_two_nonneg`` 和 ``eq_zero_of_pow_eq_zero`` 来证明一个辅助引理。
TEXT. -/
-- QUOTE:
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by sorry
  eq_zero_of_pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  eq_zero_of_pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

/- TEXT:
在 Lean 中，双蕴含具有双重身份。
你可以将其视为合取并分别使用其两个
部分。
但 Lean 也知道它是命题之间的自反、对称
和传递关系，
你也可以将其与 ``calc`` 和 ``rw`` 一起使用。
将一个命题重写为
一个等价的命题通常很方便。
在下一个例子中，我们使用 ``abs_lt`` 将
形如 ``|x| < y`` 的表达式替换
为等价表达式 ``- y < x ∧ x < y``，
在其后的例子中我们使用 ``Nat.dvd_gcd_iff``
将形如 ``m ∣ Nat.gcd n k`` 的表达式替换为等价表达式 ``m ∣ n ∧ m ∣ k``。
TEXT. -/
section

-- QUOTE:
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
-- QUOTE.

end

/- TEXT:
看看你能否使用 ``rw`` 与下面的定理
来提供一个简短的证明，说明取负不是
非递减函数。（注意 ``push_neg`` 不会
为你展开定义，因此证明中的 ``rw [Monotone]``
是必需的。）
BOTH: -/
-- QUOTE:
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

-- EXAMPLES:
example : ¬Monotone fun x : ℝ ↦ -x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num

/- TEXT:
本节剩余的练习旨在
让你对合取和双蕴含进行更多练习。
记住，*偏序*是一个
传递、自反且反对称的
二元关系。
有时会出现一个更弱的概念：
*预序*只是一个自反、传递的关系。
对于任何预序 ``≤``，
Lean 通过 ``a < b ↔ a ≤ b ∧ ¬ b ≤ a``
公理化其关联的严格预序。
证明如果 ``≤`` 是偏序，
那么 ``a < b`` 等价于 ``a ≤ b ∧ a ≠ b``：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (a b : α)

-- EXAMPLES:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

-- BOTH:
end

/- TEXT:
.. index:: simp, tactics ; simp

除了逻辑运算之外，你不需要
``le_refl``、``le_trans``
和 ``le_antisymm`` 之外的任何东西。
证明即使在 ``≤``
仅被假设为预序的情况下，
我们也能证明严格序是反自反
且传递的。
在第二个例子中，
为了方便，我们使用简化器而不是 ``rw``
来用 ``≤`` 和 ``¬`` 表示 ``<``。
我们稍后会回到简化器，
但这里我们只是依赖这样一个事实：它
会重复使用指定的引理，即使它需要
被实例化为不同的值。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Preorder α]
variable (a b c : α)

-- EXAMPLES:
example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  sorry

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  rintro ⟨h0, h1⟩
  exact h1 h0

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  constructor
  · apply le_trans h0 h2
  intro h4
  apply h1
  apply le_trans h2 h4

-- BOTH:
end
