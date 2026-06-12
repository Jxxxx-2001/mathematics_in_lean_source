-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

/- TEXT:
.. _negation:

否定
--------

符号 ``¬`` 用于表达否定，
因此 ``¬ x < y`` 表示 ``x`` 不小于 ``y``，
``¬ x = y``（或等价地，``x ≠ y``）表示
``x`` 不等于 ``y``，
而 ``¬ ∃ z, x < z ∧ z < y`` 表示不存在一个 ``z``
严格介于 ``x`` 和 ``y`` 之间。
在 Lean 中，记号 ``¬ A`` 是 ``A → False`` 的缩写，
你可以将其理解为 ``A`` 蕴含一个矛盾。
实际上，这意味着你已经知道
如何处理否定：
你可以通过引入一个假设 ``h : A``
并证明 ``False`` 来证明 ``¬ A``，
而如果你有 ``h : ¬ A`` 和 ``h' : A``，
那么将 ``h`` 应用于 ``h'`` 就得到 ``False``。

为了说明这一点，考虑严格序的
反自反性原理 ``lt_irrefl``，
它表示对每个 ``a`` 有 ``¬ a < a``。
反对称性原理 ``lt_asymm`` 表示
``a < b → ¬ b < a``。让我们证明 ``lt_asymm``
可以从 ``lt_irrefl`` 推出。
TEXT. -/
-- BOTH:
section
variable (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
-- QUOTE.

/- TEXT:
.. index:: this, have, tactics ; have, from, tactics ; from

这个例子引入了几个新技巧。
首先，当你使用 ``have`` 而不提供
标签时，
Lean 使用名称 ``this``，
提供了引用它的便捷方式。
因为证明很短，我们给出了一个显式证明项。
但在这个证明中你真正应该关注的是
``intro`` 策略的结果，
它留下了一个 ``False`` 的目标，
以及我们最终通过将 ``lt_irrefl`` 应用于
``a < a`` 的证明来证明 ``False`` 的事实。

这是另一个例子，使用了上一节定义的
谓词 ``FnHasUb``，
它表示一个函数有上界。
TEXT. -/
-- BOTH:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
-- QUOTE.

/- TEXT:
记住，当目标可以从上下文中的线性方程和
不等式中推出时，使用 ``linarith``
通常很方便。

看看你能否用类似的方法证明以下命题：
TEXT. -/
-- QUOTE:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have := ha x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

/- TEXT:
Mathlib 提供了许多有用的定理来关联序关系
和否定：
TEXT. -/
-- QUOTE:
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
-- QUOTE.

/- TEXT:
回忆谓词 ``Monotone f``，
它表示 ``f`` 是非递减的。
使用上面列出的一些定理来证明以下命题：
TEXT. -/
-- QUOTE:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge (h h'')

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h'' h

/- TEXT:
我们可以证明，如果将上一个片段中的第一个例子
的 ``<`` 替换为 ``≤``，则无法证明。
注意我们可以通过给出反例来证明一个全称量化
命题的否定。
完成这个证明。
TEXT. -/
-- QUOTE:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

/- TEXT:
.. index:: let, tactics ; let

这个例子引入了 ``let`` 策略，
它向上下文中添加一个*局部定义*。
如果你将光标放在 ``let`` 命令之后，
在目标窗口中你会看到定义
``f : ℝ → ℝ := fun x ↦ 0`` 已被添加到上下文中。
Lean 会在需要时展开 ``f`` 的定义。
特别地，当我们用 ``le_refl`` 证明 ``f 1 ≤ f 0`` 时，
Lean 将 ``f 1`` 和 ``f 0`` 归约为 ``0``。

使用 ``le_of_not_gt`` 证明以下命题：
TEXT. -/
-- QUOTE:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

-- BOTH:
end

/- TEXT:
我们刚刚完成的许多证明中隐含了这样一个事实：
如果 ``P`` 是任意性质，
说没有任何东西具有性质 ``P``
等同于说所有东西都不具有
性质 ``P``，
而说并非所有东西都具有性质 ``P``
等价于说存在某物不具有性质 ``P``。
换句话说，以下所有四个蕴含
都是有效的（但其中一个不能用我们目前所解释的方法证明）：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} (P : α → Prop) (Q : Prop)

-- EXAMPLES:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply h'

/- TEXT:
第一个、第二个和第四个很容易用你已经见过的方法
证明。
我们鼓励你试一试。
然而，第三个更困难，
因为它是从一个对象不存在的矛盾事实
推出该对象存在。
这是*经典*数学推理的一个实例。
我们可以使用反证法
来证明第三个蕴含，如下所示。
TEXT. -/
-- QUOTE:
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
-- QUOTE.

/- TEXT:
.. index:: by_contra, tactics ; by_contra and by_contradiction,

确保你理解这是如何工作的。
``by_contra`` 策略
允许我们通过假设 ``¬ Q``
并推导出矛盾来证明目标 ``Q``。
事实上，它等价于使用
等价关系 ``not_not : ¬ ¬ Q ↔ Q``。
确认你可以使用 ``by_contra`` 证明
这个等价关系的正向，
而反向可以从
否定的通常规则推出。
TEXT. -/
-- QUOTE:
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

-- BOTH:
end

/- TEXT:
使用反证法来证明以下命题，
它是我们上面证明的一个蕴含的逆命题。
（提示：首先使用 ``intro``。）
TEXT. -/
-- BOTH:
section
variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

/- TEXT:
.. index:: push_neg, tactics ; push_neg

处理前面带有一个否定的复合命题通常很繁琐，
而数学中一个常见的模式是将这种
命题替换为否定已被向内推进
的等价形式。
为了便于这样做，Mathlib 提供了 ``push_neg`` 策略，
它以这种方式重述目标（这包括
将 ``¬ ¬A`` 简化为 ``A``）。
命令 ``push_neg at h`` 重述假设 ``h``。
TEXT. -/
-- QUOTE:
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
-- QUOTE.

/- TEXT:
在第二个例子中，我们使用 dsimp 来
展开 ``FnHasUb`` 和 ``FnUb`` 的定义。
（我们需要使用 ``dsimp`` 而不是 ``rw``
来展开 ``FnUb``，
因为它出现在量词的作用域内。）
你可以验证在上面
关于 ``¬∃ x, P x`` 和 ``¬∀ x, P x`` 的例子中，
``push_neg`` 策略做了预期的事情。
甚至不需要知道如何使用合取
符号，
你应该就能使用 ``push_neg``
来证明以下命题：
TEXT. -/
-- QUOTE:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg at h
  exact h

/- TEXT:
.. index:: contrapose, tactics ; contrapose

Mathlib 还有一个策略 ``contrapose``，
它将目标 ``A → B`` 转换为 ``¬B → ¬A``。
类似地，给定一个从
假设 ``h : A`` 证明 ``B`` 的目标，
``contrapose h`` 留下从假设 ``¬B`` 证明
``¬A`` 的目标。
使用 ``contrapose!`` 代替 ``contrapose``
还会对目标和相关的
假设应用 ``push_neg``。
TEXT. -/
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
-- QUOTE.

-- BOTH:
end

/- TEXT:
我们还没有解释 ``constructor`` 命令
或其后分号的使用，
但我们将在下一节中做这件事。

我们以*爆炸原理*（ex falso）
来结束本节，
它表示从矛盾可以推出任何东西。
在 Lean 中，这由 ``False.elim`` 表示，
它对任何命题 ``P`` 建立 ``False → P``。
这可能看起来像一个奇怪的原理，
但它经常出现。
我们经常通过分情况来证明一个定理，
有时我们可以证明其中一种情况
是矛盾的。
在这种情况下，我们需要断言这个矛盾
能推出目标，以便我们继续处理下一种情况。
（我们将在 :numref:`disjunction` 中看到
分情况推理的实例。）

.. index:: exfalso, contradiction, absurd, tactics ; exfalso, tactics ; contradiction

Lean 提供了多种在达到矛盾后
闭合目标的方法。
TEXT. -/
section
variable (a : ℕ)

-- QUOTE:
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
-- QUOTE.

end

/- TEXT:
``exfalso`` 策略将当前目标替换为
证明 ``False`` 的目标。
给定 ``h : P`` 和 ``h' : ¬ P``，
项 ``absurd h h'`` 可以推出任何命题。
最后，``contradiction`` 策略尝试通过
在假设中寻找矛盾来闭合目标，
例如一对 ``h : P`` 和 ``h' : ¬ P`` 的形式。
当然，在这个例子中，``linarith`` 也能起作用。
TEXT. -/
