-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

/- TEXT:
.. _implication_and_the_universal_quantifier:

蕴含与全称量词
----------------------------------------

考虑 ``#check`` 后面的语句：
TEXT. -/
-- QUOTE:
#check ∀ x : ℝ, 0 ≤ x → |x| = x
-- QUOTE.

/- TEXT:
用文字来说，就是“对于每个实数 ``x``，如果 ``0 ≤ x``，那么
``x`` 的绝对值等于 ``x``”。
我们也可以有更复杂的语句，例如：
TEXT. -/
-- QUOTE:
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
-- QUOTE.

/- TEXT:
用文字来说，就是“对于每个 ``x``、``y`` 和 ``ε``，
如果 ``0 < ε ≤ 1``，``x`` 的绝对值小于 ``ε``，
且 ``y`` 的绝对值小于 ``ε``，
那么 ``x * y`` 的绝对值小于 ``ε``”。
在 Lean 中，在一系列蕴含中，隐式括号向右结合。
因此上面的表达式意味着
“如果 ``0 < ε``，那么如果 ``ε ≤ 1``，那么如果 ``|x| < ε``……”
因此，该表达式表明所有
假设一起蕴含结论。

你已经看到，尽管这个语句中的全称量词
作用于对象，而蕴含箭头引入假设，
Lean 对两者的处理方式非常相似。
特别地，如果你已经证明了这种形式的定理，
你可以以同样的方式将其应用于对象和假设。
我们将以下述语句为例，稍后我们会帮你证明它：
TEXT. -/
-- QUOTE:
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
你也已经看到，在 Lean 中，
当量化的变量可以从后续假设中推断出来时，
通常用花括号将它们标记为隐式变量。
当我们这样做时，我们可以只将引理应用于假设，而不需要
提及这些对象。
TEXT. -/
-- QUOTE:
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
在这个阶段，你也知道如果使用
``apply`` 策略将 ``my_lemma``
应用于形如 ``|a * b| < δ`` 的目标，
你会留下新的目标，需要你证明
每个假设。

.. index:: intro, tactics; intro

要证明一个像这样的语句，使用 ``intro`` 策略。
看看它在这个例子中的作用：
TEXT. -/
-- QUOTE:
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
-- QUOTE.

/- TEXT:
我们可以为全称量化变量使用任何名称；
它们不必是 ``x``、``y`` 和 ``ε``。
注意我们必须引入这些变量，
即使它们被标记为隐式：
使它们隐式意味着我们在编写*使用* ``my_lemma`` 的表达式时省略它们，
但它们仍然是我们正在证明的语句中
必不可少的部分。
在 ``intro`` 命令之后，
目标就像我们上一节那样
在冒号*之前*列出所有变量和假设时一样。
稍后我们将看到为什么有时
需要在证明开始之后引入变量和假设。

为了帮助你证明这个引理，我们给你一个开头：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
/- EXAMPLES:
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

SOLUTIONS: -/
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
    _ < 1 * ε := by apply mul_lt_mul_of_pos_right _ epos; linarith
    _ = ε := by apply one_mul
-- QUOTE.

/- TEXT:
使用定理 ``abs_mul``、``mul_le_mul``、``abs_nonneg``、
``mul_lt_mul_of_pos_right`` 和 ``one_mul`` 完成证明。
记住你可以使用 Ctrl-空格（Mac 上是 Cmd-空格）补全来查找这类定理。
也请记住你可以使用 ``.mp`` 和 ``.mpr``
或 ``.1`` 和 ``.2`` 来提取一个当且仅当语句的
两个方向。

全称量词常常隐藏在定义中，
Lean 会在必要时展开定义来暴露它们。
例如，让我们定义两个谓词
``FnUb f a`` 和 ``FnLb f a``，
其中 ``f`` 是从实数到实数的函数，
``a`` 是实数。
第一个表示 ``a`` 是 ``f`` 的值的上界，
第二个表示 ``a`` 是 ``f`` 的值的下界。
BOTH: -/
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
-- QUOTE.

/- TEXT:
.. index:: lambda abstraction

在下一个例子中，``fun x ↦ f x + g x`` 是
将 ``x`` 映射到 ``f x + g x`` 的函数。从表达式 ``f x + g x``
到这个函数的转换在类型论中称为 lambda 抽象。
BOTH: -/
section
variable (f g : ℝ → ℝ) (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
-- QUOTE.

/- TEXT:
.. index:: dsimp, tactics ; dsimp, change, tactics ; change

对目标 ``FnUb (fun x ↦ f x + g x) (a + b)`` 应用 ``intro``
会强制 Lean 展开 ``FnUb`` 的定义
并为全称量词引入 ``x``。
此时目标是 ``(fun (x : ℝ) ↦ f x + g x) x ≤ a + b``。
但将 ``(fun x ↦ f x + g x)`` 应用于 ``x`` 应该得到 ``f x + g x``，
而 ``dsimp`` 命令执行了这个化简。
（"d" 代表 "definitional"（定义性的）。）
你可以删除该命令，证明仍然有效；
Lean 无论如何都需要执行这种归约
才能理解下一个 ``apply``。
``dsimp`` 命令只是使目标更具可读性
并帮助我们弄清下一步该做什么。
另一种选择是使用 ``change`` 策略，
写成 ``change f x + g x ≤ a + b``。
这有助于使证明更具可读性，
并让你对目标的变换有更多的控制。

证明的其余部分是常规的。
最后两个 ``apply`` 命令强制 Lean 展开假设中
``FnUb`` 的定义。
尝试完成以下类似的证明：
TEXT. -/
-- QUOTE:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  apply nna

-- BOTH:
end

/- TEXT:
尽管我们为从实数到实数的函数定义了 ``FnUb`` 和 ``FnLb``，
你应该意识到这些定义和证明
要普遍得多。
这些定义对于任何两个类型的函数都有意义，
只要陪域上有序的概念。
检查定理 ``add_le_add`` 的类型可以看出，它适用于
任何“有序加法交换幺半群”结构；
这种结构的具体含义现在并不重要，
但值得知道的是，自然数、整数、有理数
和实数都是它的实例。
因此，如果我们在这种一般性层次上证明定理 ``fnUb_add``，
它将适用于所有这些实例。
TEXT. -/
section
-- QUOTE:
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
-- QUOTE.

end

/- TEXT:
你已经在 :numref:`proving_identities_in_algebraic_structures` 一节中
见过这样的方括号，
尽管我们还没有解释它们的含义。
为了具体起见，我们大多数例子中
将坚持使用实数，
但值得知道的是 Mathlib 包含了
在高度一般性层次上工作的定义和定理。

.. index:: monotone function

作为隐藏的全称量词的另一个例子，
Mathlib 定义了一个谓词 ``Monotone``，
表示一个函数在其参数上是非递减的：
TEXT. -/
-- QUOTE:
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
-- QUOTE.

/- TEXT:
性质 ``Monotone f`` 恰好被定义为冒号后面的表达式。
我们需要在 ``h`` 前面放 ``@`` 符号，因为
如果不放，
Lean 会展开 ``h`` 的隐式参数并插入占位符。

证明关于单调性的命题
涉及使用 ``intro`` 来引入两个变量，
例如 ``a`` 和 ``b``，以及假设 ``a ≤ b``。
要*使用*单调性假设，
你可以将其应用于合适的参数和假设，
然后将得到的表达式应用于目标。
或者，你可以将其应用于目标，让 Lean 帮你
反向工作，将剩余的假设
显示为新的子目标。
BOTH: -/
section
variable (f g : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
-- QUOTE.

/- TEXT:
当证明如此简短时，通常更方便
给出证明项。
要描述一个临时引入对象
``a`` 和 ``b`` 以及假设 ``aleb`` 的证明，
Lean 使用记号 ``fun a b aleb ↦ ...``。
这类似于 ``fun x ↦ x^2`` 这样的表达式
通过临时命名一个对象 ``x``
然后用它来描述一个值来描述一个函数。
因此前一个证明中的 ``intro`` 命令
对应于下一个证明项中的 lambda 抽象。
然后 ``apply`` 命令对应于构建
定理对其参数的应用。
TEXT. -/
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun _a _b aleb ↦ add_le_add (mf aleb) (mg aleb)
-- QUOTE.

/- TEXT:
这是一个有用的技巧：如果你开始编写
证明项 ``fun a b aleb ↦ _``，
在表达式其余部分的位置使用下划线，
Lean 会标记一个错误，
表示它无法猜测该表达式的值。
如果你查看 VS Code 中的 Lean InfoView 窗口或
将鼠标悬停在波浪线错误标记上，
Lean 会显示剩余表达式
需要解决的目标。

你会注意到 Lean 对上述证明输出警告，说
`a` 和 `b` 没有在函数体中使用。
这是一个通用机制，例如有助于避免
定理中存在不必要的假设。在这里，它其实没有告诉我们
任何有用的信息。我们可以通过写
`set_option linter.unusedVariables false`
来在当前节的末尾之前禁用此警告，
或者通过在该例子上面写
`set_option linter.unusedVariables false in`
来仅在该例子中禁用。

我们也可以将 `a` 和 `b` 替换为下划线，告诉 Lean 我们不想
给它们命名。然后 Lean 会使用自动生成的不可访问名称，
如 `x✝`。或者，我们可以在名称前加下划线
来告诉 Lean 我们不打算使用它们。


尝试用策略或证明项证明以下例子：
TEXT. -/
-- QUOTE:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun _a _b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  apply aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun _a _b aleb ↦ mf (mg aleb)

/- TEXT:
这里还有一些例子。
从 :math:`\Bbb R` 到
:math:`\Bbb R` 的函数 :math:`f` 如果对每个 :math:`x`
满足 :math:`f(-x) = f(x)`，则称为*偶函数*；
如果对每个 :math:`x` 满足 :math:`f(-x) = -f(x)`，则称为*奇函数*。
以下例子形式化地定义了这两个概念
并证明了关于它们的一个事实。
你可以完成其余证明。
TEXT. -/
-- QUOTE:
-- BOTH:
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

-- EXAMPLES:
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ← ef]

-- BOTH:
end

/- TEXT:
.. index:: erw, tactics ; erw

第一个证明可以使用 ``dsimp`` 或 ``change`` 来缩短，
以消除 lambda 抽象。
但你可以检查，除非我们显式地消除 lambda 抽象，
否则后续的 ``rw`` 将无法工作，
因为否则它无法在表达式中找到模式 ``f x`` 和 ``g x``。
与其他一些策略不同，``rw`` 在语法层面操作，
它不会为你展开定义或应用归约
（它有一个变体叫做 ``erw``，在这个方向上会更努力一些，
但也不会努力太多）。

一旦你知道如何发现它们，你可以到处找到
隐式的全称量词。

Mathlib 包含一个用于操作集合的良好库。请记住，Lean 不
使用基于集合论的基础，因此这里的“集合”一词具有通常的含义，
即某一给定类型 ``α`` 的数学对象的汇集。
如果 ``x`` 的类型是 ``α``，``s`` 的类型是 ``Set α``，那么 ``x ∈ s`` 是一个命题，
断言 ``x`` 是 ``s`` 的一个元素。如果 ``y`` 具有某个不同的类型 ``β``，那么
表达式 ``y ∈ s`` 没有意义。这里“没有意义”意味着“没有类型，因此 Lean 不接受
其为良构的语句”。这与例如 Zermelo-Fraenkel 集合论形成对比，
在 ZF 中 ``a ∈ b`` 对于任何数学对象 ``a`` 和 ``b`` 都是良构的语句。
例如 ``sin ∈ cos`` 在 ZF 中是一个良构的语句。集合论基础的这一缺陷
是不在旨在通过检测无意义表达式来辅助我们的证明助手中使用它的重要动机。
在 Lean 中，``sin`` 的类型是 ``ℝ → ℝ``，``cos`` 的类型是
``ℝ → ℝ``，它不等于 ``Set (ℝ → ℝ)``，即使展开定义之后也是如此，因此语句
``sin ∈ cos`` 没有意义。
你也可以使用 Lean 来研究集合论本身。例如连续统假设
相对于 Zermelo-Fraenkel 公理的独立性已经在 Lean 中被形式化。但这种
集合论的元理论完全超出了本书的范围。

如果 ``s`` 和 ``t`` 的类型都是 ``Set α``，
那么子集关系 ``s ⊆ t`` 被定义为
``∀ {x : α}, x ∈ s → x ∈ t``。
量词中的变量被标记为隐式，这样
给定 ``h : s ⊆ t`` 和 ``h' : x ∈ s``，
我们可以写 ``h h'`` 作为 ``x ∈ t`` 的理由。
下面的例子提供了子集关系自反性的
一个策略证明和一个证明项，
并要求你对传递性做同样的事情。
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α : Type*} (r s t : Set α)

-- EXAMPLES:
example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun _x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  apply ssubt
  apply rsubs
  apply xr

theorem Subset.transαα : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt _x xr ↦ ssubt (rsubs xr)

-- BOTH:
end

/- TEXT:
正如我们为函数定义了 ``FnUb``，
我们可以定义 ``SetUb s a`` 来表示 ``a``
是集合 ``s`` 的一个上界，
假设 ``s`` 是某个具有关联序关系的
类型的元素集合。
在下一个例子中，我们要求你证明
如果 ``a`` 是 ``s`` 的一个界，且 ``a ≤ b``，
那么 ``b`` 也是 ``s`` 的一个界。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- EXAMPLES:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'

-- BOTH:
end

/- TEXT:
.. index:: injective function

我们以最后一个重要的例子结束本节。
一个函数 :math:`f` 被称为*单射*，如果对于
每个 :math:`x_1` 和 :math:`x_2`，
如果 :math:`f(x_1) = f(x_2)` 那么 :math:`x_1 = x_2`。
Mathlib 用 ``x₁`` 和 ``x₂`` 为隐式定义 ``Function.Injective f``。
下一个例子表明，在实数上，
任何加上一个常数的函数都是单射的。
然后我们要求你证明乘以一个非零
常数也是单射的，使用例子中的引理名称作为灵感来源。
记住你应该在猜出引理名称的开头后使用 Ctrl-空格补全。
TEXT. -/
-- BOTH:
section

-- QUOTE:
open Function

-- EXAMPLES:
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

/- TEXT:
最后，证明两个单射函数的复合也是单射的：
BOTH: -/
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h

-- BOTH:
end
