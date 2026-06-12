-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _proving_identities_in_algebraic_structures:

在代数结构中证明恒等式
------------------------------------------

.. index:: ring (algebraic structure)

在数学上，一个环由一组对象 :math:`R`、
运算 :math:`+` :math:`\times`、常数 :math:`0`
和 :math:`1`，以及运算 :math:`x \mapsto -x` 组成，满足：

* :math:`R` 配备 :math:`+` 构成一个 *阿贝尔群*，以 :math:`0`
  为加法单位元，取负为逆元。
* 乘法是结合的，以 :math:`1` 为单位元，
  且乘法对加法满足分配律。

在 Lean 中，对象的集合被表示为一个 *类型*，``R``。
环公理如下：
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-- QUOTE.

end

/- TEXT:
你将在后面了解更多关于第一行中方括号的含义，
但就目前而言，
只需知道该声明给了我们一个类型 ``R``，
以及 ``R`` 上的环结构。
Lean 随后允许我们对 ``R`` 的元素使用通用的环记号，
并使用关于环的定理库。

其中一些定理的名称应该看起来很熟悉：
它们正是我们在上一节中用于实数计算的定理。
Lean 不仅擅长证明关于具体数学结构
（如自然数和整数）的事情，
也擅长证明关于抽象结构的事情，
这些结构通过公理刻画，例如环。
此外，Lean 支持对抽象结构和具体结构
进行 *通用推理*，
并且可以被训练来识别适当的实例。
因此，任何关于环的定理都可以应用于具体的环，
如整数 ``ℤ``、有理数 ``ℚ``
和复数 ``ℂ``。
它也可以应用于任何扩展环的抽象结构的实例，
例如任何有序环或任何域。

.. index:: commutative ring

然而，并非实数所有重要的性质都在
任意环中成立。
例如，实数上的乘法
是交换的，
但这并非普遍成立。
如果你上过线性代数课程，
你会认识到，对于每个 :math:`n`，
实数的 :math:`n` 乘 :math:`n` 矩阵
构成一个环，其中交换律通常不成立。如果我们声明 ``R`` 是一个
*交换* 环，实际上，上一节中所有的定理
在我们用 ``R`` 替换 ``ℝ`` 后仍然成立。
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
我们留给你去验证所有其他证明都能不加修改地通过。
注意，当证明很短时，如 ``by ring`` 或 ``by linarith``
或 ``by sorry``，
将其放在 ``by`` 的同一行是很常见的（也是允许的）。
良好的证明写作风格应在简洁性和可读性之间取得平衡。

本节的目标是巩固你在上一节中培养的技能，
并将其应用于关于环的公理化推理。
我们将从上面列出的公理开始，
并用它们推导出其他事实。
我们证明的大多数事实已经在 Mathlib 中。
我们会给我们要证明的版本取相同的名字，
以帮助你学习库的内容
以及命名约定。

.. index:: namespace, open, command ; open

Lean 提供了一种类似于编程语言中使用的组织结构机制：
当一个定义或定理 ``foo`` 在 *命名空间*
``bar`` 中被引入时，它的全名是 ``bar.foo``。
命令 ``open bar`` 稍后会 *打开* 该命名空间，
这允许我们使用较短的名称 ``foo``。
为了避免名称冲突导致的错误，
在下一个例子中，我们将库定理的自制版本
放在一个名为 ``MyRing`` 的新命名空间中。

下一个例子表明，我们不需要 ``add_zero`` 或 ``add_neg_cancel``
作为环公理，因为它们可以从其他公理推导出来。
TEXT. -/
-- QUOTE:
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing
-- QUOTE.

/- TEXT:
其最终效果是，我们可以临时重证库中的一个定理，
然后在那之后继续使用库版本。
但不要作弊！
在接下来的练习中，请谨慎只使用
我们在本节中早先证明过的关于环的一般事实。

（如果你仔细注意，你可能已经注意到我们把
``(R : Type*)`` 中的圆括号改为
``{R : Type*}`` 中的花括号了。
这将 ``R`` 声明为 *隐式参数*。
我们稍后会解释这意味着什么，
但在此期间不必担心。）

这是一个有用的定理：
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]
-- QUOTE.

/- TEXT:
证明对应的版本：
TEXT. -/
-- 证明这些：
-- QUOTE:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_neg_cancel_rightαα (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

/- TEXT:
使用这些来证明以下内容：
TEXT. -/
-- QUOTE:
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_left_cancelαα {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancelαα {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

/- TEXT:
有了充分的规划，你可以用三步重写完成每一个。

.. index:: implicit argument

我们现在来解释花括号的用法。
想象一下，你处于这样一种情境中：你的上下文中有 ``a``、``b`` 和 ``c``，
以及一个假设 ``h : a + b = a + c``，
你想要得出 ``b = c`` 的结论。
在 Lean 中，你可以将定理应用于假设和事实，
就像你将它们应用于对象一样，
所以你可能会认为 ``add_left_cancel a b c h`` 是
``b = c`` 这个事实的证明。
但请注意，显式写出 ``a``、``b`` 和 ``c``
是多余的，因为假设 ``h`` 清楚地表明了
那些是我们心中所想的对象。
在这种情况下，多打几个字符并不麻烦，
但如果我们要将 ``add_left_cancel`` 应用于更复杂的表达式，
写出它们将是繁琐的。
在类似这样的情况下，
Lean 允许我们将参数标记为 *隐式的*，
意味着它们应该被省略，并通过其他方式推断出来，
例如后续的参数和假设。
``{a b c : R}`` 中的花括号正是做到了这一点。
因此，根据上面定理的陈述，
正确的表达式只是 ``add_left_cancel h``。

为了说明，让我们证明 ``a * 0 = 0``
可以从环公理推导出来。
TEXT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
-- QUOTE.

/- TEXT:
.. index:: have, tactics ; have

我们使用了一个新技巧！
如果你逐步执行这个证明，
你可以看到发生了什么。
``have`` 策略引入了一个新目标，
``a * 0 + a * 0 = a * 0 + 0``，
其上下文与原目标相同。
下一行缩进的事实表明 Lean
期望一个策略块来证明这个
新目标。
因此，缩进促进了模块化的证明风格：
缩进的子证明建立了 ``have`` 引入
的目标。
之后，我们回到证明原始目标，
但此时已添加了一个新的假设 ``h``：
既然已经证明了它，我们现在可以自由地使用它。
此时，目标正好是 ``add_left_cancel h`` 的结果。

.. index:: apply, tactics ; apply, exact, tactics ; exact

我们同样也可以用
``apply add_left_cancel h`` 或 ``exact add_left_cancel h`` 来结束证明。
``exact`` 策略接受一个完全证明当前目标的
证明项作为参数，不创建任何新目标。``apply`` 策略是一个变体，
其参数不一定是一个完整的证明。缺失的部分
要么由 Lean 自动推断，要么成为需要证明的新目标。
虽然 ``exact`` 策略在技术上是冗余的，因为它严格弱于
``apply``，但它使证明脚本对人类读者来说稍微更清晰，
并且在库演变时更容易维护。

请记住，乘法并不假设是可交换的，
因此下面的定理也需要一些工夫。
TEXT. -/
-- QUOTE:
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem zero_mulαα (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

/- TEXT:
到现在，你也应该能够在下一个练习中用证明
替换每一个 ``sorry``，
仍然只使用我们在本节中已经建立的关于环的事实，
以及公理 ``eq_symm``。
TEXT. -/
-- QUOTE:
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem neg_eq_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : a = -b := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [add_comm, h]

theorem neg_zeroαα : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_negαα (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

-- BOTH:
end MyRing

/- TEXT:
我们不得不在第三个定理中使用标注 ``(-0 : R)`` 而非 ``0``，
因为如果不指定 ``R``，
Lean 不可能推断我们心中所想的是哪个 ``0``，
默认情况下它会被解释为自然数。

在 Lean 中，环中的减法可证明等于
加法逆元的加法。
TEXT. -/
-- 示例。
section
variable {R : Type*} [Ring R]

-- QUOTE:
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
-- QUOTE.

end

/- TEXT:
在实数上，它是按那种方式 *定义* 的：
TEXT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- TEXT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

证明项 ``rfl`` 是"自反性"的缩写。
将其作为 ``a - b = a + -b`` 的证明呈现会迫使 Lean
展开定义并识别两边是相同的。
``rfl`` 策略做同样的事情。
这是 Lean 底层逻辑中所称的 *定义相等* 的一个实例。
这意味着不仅可以用 ``sub_eq_add_neg`` 重写
来替换 ``a - b = a + -b``，
而且在某些上下文中，当处理实数时，
你可以互换使用方程的两边。
例如，你现在有足够的信息来证明上一节中的
``self_sub`` 定理：
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem self_sub (a : R) : a - a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem self_subαα (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

/- TEXT:
证明你可以使用 ``rw`` 来证明这个，
但如果你将任意环 ``R`` 替换为
实数，你也可以使用
``apply`` 或 ``exact`` 来证明它。

Lean 知道 ``1 + 1 = 2`` 在任何环中成立。
通过一点努力，
你可以用它来证明上一节中的定理
``two_mul``：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- EXAMPLES:
theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem two_mulαα (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

-- BOTH:
end MyRing

/- TEXT:
.. index:: group (algebraic structure)

在本节结束时，我们注意到，我们上面建立的关于
加法和取负的一些事实并不
需要环公理的全部力量，甚至不需要
加法的交换性。更弱的概念 *群*
可以按如下公理化：
TEXT. -/
section
-- QUOTE:
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)
-- QUOTE.

end

/- TEXT:
当群运算是可交换的时，通常使用加法记号，
否则使用乘法记号。
因此 Lean 定义了乘法版本以及
加法版本（以及它们的阿贝尔变体，
``AddCommGroup`` 和 ``CommGroup``）。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {G : Type*} [Group G]

-- EXAMPLES:
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
-- QUOTE.

/- TEXT:
如果你感到自信，尝试仅使用这些公理证明以下关于群的事实。
你需要在过程中证明一些辅助引理。
我们在本节中完成的证明提供了一些提示。
TEXT. -/
-- BOTH:
namespace MyGroup

-- EXAMPLES:
-- QUOTE:
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem mul_inv_cancelαα (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_oneαα (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_revαα (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

-- BOTH:
end MyGroup

end

/- TEXT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

显式调用这些引理是很繁琐的，因此 Mathlib 提供了
类似于 `ring` 的策略来覆盖大多数使用场景：`group`
用于非交换乘法群，`abel` 用于阿贝尔
加法群，`noncomm_ring` 用于非交换环。
看起来可能有些奇怪，代数结构被称为
`Ring` 和 `CommRing`，而策略却命名为
`noncomm_ring` 和 `ring`。这有部分历史原因，
但也是为了方便起见，用更短的名称来命名
处理交换环的策略，因为它更常用。
TEXT. -/
