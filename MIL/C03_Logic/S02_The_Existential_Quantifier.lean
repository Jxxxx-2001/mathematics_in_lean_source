-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

/- TEXT:
.. _the_existential_quantifier:

存在量词
--------------------------

存在量词，可以在 VS Code 中输入 ``\ex``，
用于表示短语“存在”。
Lean 中的形式表达式 ``∃ x : ℝ, 2 < x ∧ x < 3`` 表示
存在一个介于 2 和 3 之间的实数。
（我们将在 :numref:`conjunction_and_biimplication` 中讨论合取符号 ``∧``。）
证明这样一个命题的标准方法是展示一个实数
并证明它具有所述的性质。
数字 2.5，我们可以输入为 ``5 / 2``
或 ``(5 : ℝ) / 2``（当 Lean 无法从上下文推断出我们
指的是实数时），具有所需的性质，
而 ``norm_num`` 策略可以证明它满足该描述。

.. index:: use, tactics ; use

我们有几种方法可以将信息组合在一起。
给定一个以存在量词开头的目标，
``use`` 策略用于提供对象，
留下证明该性质的目标。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
-- QUOTE.

/- TEXT:
你可以将证明以及数据一同提供给 ``use`` 策略：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
-- QUOTE.

/- TEXT:
事实上，``use`` 策略也会自动尝试使用可用的假设。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
-- QUOTE.

/- TEXT:
.. index:: anonymous constructor

或者，我们可以使用 Lean 的*匿名构造子*记号
来构造一个存在量词的证明。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
-- QUOTE.

/- TEXT:
注意这里没有 ``by``；这里我们给出的是一个显式证明项。
左右尖括号，
可以分别输入为 ``\<`` 和 ``\>``，
告诉 Lean 使用适合当前目标
的构造方式
将给定数据组合在一起。
我们可以不先进入策略模式就使用该记号：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
-- QUOTE.

/- TEXT:
现在我们知道如何*证明*一个存在命题了。
但我们如何*使用*一个存在命题呢？
如果我们知道存在一个具有特定性质的对象，
我们应该能够给任意一个这样的对象命名
并对其进行推理。
例如，回忆上一节的谓词 ``FnUb f a`` 和 ``FnLb f a``，
它们分别表示 ``a`` 是 ``f`` 的一个上界或下界。
我们可以使用存在量词来表示“``f`` 有界”
而不指定界限：
TEXT. -/
-- BOTH:
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
-- QUOTE.

/- TEXT:
我们可以使用上一节的定理 ``FnUb_add``
来证明如果 ``f`` 和 ``g`` 有上界，
那么 ``fun x ↦ f x + g x`` 也有上界。
TEXT. -/
-- BOTH:
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

-- QUOTE:
variable {f g : ℝ → ℝ}

-- EXAMPLES:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
-- QUOTE.

/- TEXT:
.. index:: cases, tactics ; cases

``rcases`` 策略解包存在量词中
包含的信息。
形如 ``⟨a, ubfa⟩`` 的注解，使用与
匿名构造子相同的尖括号书写，
被称为*模式*，它们描述了我们在解包主参数时
期望找到的信息。
给定假设 ``ubf``，即 ``f`` 存在一个上界，
``rcases ubf with ⟨a, ubfa⟩`` 向上下文中添加了一个新变量 ``a``
作为上界，
以及它满足给定性质的假设 ``ubfa``。
目标保持不变；
改变的是我们现在可以使用
新对象和新假设
来证明目标。
这是数学中常见的推理方法：
我们解包由某个假设断言或蕴含其存在的对象，
然后用它来建立其他事物的存在。

尝试使用这种方法来证明以下命题。
你可能会发现将上一节的一些例子
转化为命名定理会很有用，
就像我们对 ``fn_ub_add`` 所做的那样，
或者你可以将参数直接插入
到证明中。
TEXT. -/
-- QUOTE:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

/- TEXT:
.. index:: rintro, tactics ; rintro, rcases, tactics ; rcases

``rcases`` 中的 "r" 代表 "recursive"（递归），因为它允许
我们使用任意复杂的模式来解包嵌套数据。
``rintro`` 策略
是 ``intro`` 和 ``rcases`` 的组合：
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
事实上，Lean 也支持在表达式和证明项中
使用模式匹配的 fun：
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

-- BOTH:
end

/- TEXT:
在假设中解包信息这项任务
非常重要，因此 Lean 和 Mathlib 提供了
多种方法来完成它。例如，``obtain`` 策略提供了直观的语法：
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
把第一条 ``obtain`` 指令理解为将 ``ubf`` 的“内容”与给定模式匹配，
并将分量赋值给命名变量。
``rcases`` 和 ``obtain`` 被称为“析构”它们的参数。

Lean 也支持与其他函数式编程语言类似的语法：
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
在第一个例子中，如果你将光标放在 ``cases ubf`` 之后，
你会看到该策略产生了一个单一目标，Lean 将其标记为
``intro``。（这个特定的名称来自构造存在命题证明的
公理化原语的内部名称。）
然后 ``case`` 策略命名了各个分量。第二个例子类似，
只是使用 ``next`` 而不是 ``case`` 意味着你可以避免提及
``intro``。最后两个例子中的 ``match`` 一词强调了
我们在这里所做的是计算机科学家所说的“模式匹配”。
注意第三个证明以 ``by`` 开头，之后 ``match`` 的策略版本
期望箭头右侧是一个策略证明。
最后一个例子是一个证明项：根本看不到策略。

在本书的其余部分，我们将坚持使用 ``rcases``、``rintro`` 和 ``obtain``
作为使用存在量词的首选方式。
但看到替代语法也无妨，特别是如果你有可能
会与计算机科学家在一起的话。

为了说明 ``rcases`` 的一种使用方式，
我们证明一个古老的数学经典结论：
如果两个整数 ``x`` 和 ``y`` 可以各自写为
两个平方数之和，
那么它们的乘积 ``x * y`` 也可以。
事实上，这个命题对任何交换环
都成立，不仅仅是整数。
在下一个例子中，``rcases`` 一次性解包了两个存在
量词。
然后我们提供将 ``x * y`` 表示为平方和
所需的魔法值作为列表给 ``use`` 语句，
并用 ``ring`` 验证它们是正确的。
TEXT. -/
section

-- QUOTE:
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

/- TEXT:
这个证明没有提供太多洞见，
但这里有一种理解它的方式。
*高斯整数*是形如 :math:`a + bi` 的数，
其中 :math:`a` 和 :math:`b` 是整数，:math:`i = \sqrt{-1}`。
高斯整数 :math:`a + bi` 的*范数*定义为
:math:`a^2 + b^2`。
因此高斯整数的范数是一个平方和，
而任何平方和都可以用这种方式表示。
上述定理反映了这样一个事实：高斯整数乘积的范数
等于它们范数的乘积：
如果 :math:`x` 是 :math:`a + bi` 的范数，
:math:`y` 是 :math:`c + di` 的范数，
那么 :math:`xy` 就是 :math:`(a + bi) (c + di)` 的范数。
我们这个神秘的证明说明了这样一个事实：
最容易形式化的证明并不总是
最清晰的证明。
在 :numref:`section_building_the_gaussian_integers` 中，
我们将为你提供定义高斯整数的方法
并用它们提供一个替代的证明。

在存在量词中解包一个等式，
然后用它来重写目标中的表达式，
这种模式经常出现，
以至于 ``rcases`` 策略提供了一个缩写：
如果你在本来该用新标识符的地方使用关键字 ``rfl``，
``rcases`` 会自动完成重写（这个技巧不适用于
模式匹配的 lambda 表达式）。
TEXT. -/
-- QUOTE:
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

end

/- TEXT:
与全称量词一样，
如果你知道如何发现它们，你可以到处找到
隐藏的存在量词。
例如，整除性隐含地是一个“存在”命题。
TEXT. -/
-- BOTH:
section
variable {a b c : ℕ}

-- EXAMPLES:
-- QUOTE:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
-- QUOTE.

/- TEXT:
这再次为一个使用 ``rcases`` 与 ``rfl`` 的
优雅场景提供了很好的设置。
在上面的证明中试试看。
感觉非常好！

然后尝试证明以下命题：
TEXT. -/
-- QUOTE:
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

-- BOTH:
end

/- TEXT:
.. index:: surjective function

另一个重要的例子是，函数 :math:`f : \alpha \to \beta`
被称为*满射*，如果对于陪域 :math:`\beta` 中的
每个 :math:`y`，
存在定义域 :math:`\alpha` 中的一个 :math:`x`，
使得 :math:`f(x) = y`。
注意这个命题同时包含一个全称量词
和一个存在量词，这解释了
为什么下一个例子既使用 ``intro`` 也使用 ``use``。
TEXT. -/
-- BOTH:
section

open Function

-- EXAMPLES:
-- QUOTE:
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
-- QUOTE.

/- TEXT:
使用定理 ``mul_div_cancel₀`` 自己尝试这个例子：
TEXT. -/
-- QUOTE:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel₀ _ h]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp

/- TEXT:
.. index:: field_simp, tactics ; field_simp

在这一点上，值得提一下有一个策略 ``field_simp``，
它通常能以有用的方式消去分母。
它可以与 ``ring`` 策略一起使用。
TEXT. -/
-- QUOTE:
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
-- QUOTE.

/- TEXT:
下一个例子通过将满射性假设
应用于一个合适的值来使用它。
注意你可以对任何表达式使用 ``rcases``，
而不仅仅是假设。
TEXT. -/
-- QUOTE:
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
-- QUOTE.

-- BOTH:
end

/- TEXT:
看看你能否使用这些方法来证明
满射函数的复合也是满射的。
TEXT. -/
-- BOTH:
section
open Function
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, rfl⟩
  rcases surjf y with ⟨x, rfl⟩
  use x

-- BOTH:
end
