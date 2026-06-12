import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/- TEXT:
.. _section_induction_and_recursion:

归纳与递归
-----------------------

自然数集合 :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`
不仅本身是根本重要的，
而且在新数学对象的构造中也起着核心作用。
Lean 的基础允许我们声明*归纳类型*，
这些类型由给定的*构造子*列表
归纳生成。
在 Lean 中，自然数的声明如下。
OMIT: -/
namespace hidden

-- QUOTE:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- QUOTE.

end hidden

/- TEXT:
你可以通过输入 ``#check Nat`` 然后
在标识符 ``Nat`` 上使用 ``ctrl-click`` 在库中找到它。
该命令指定 ``Nat`` 是由两个构造子
``zero : Nat`` 和 ``succ : Nat → Nat``
自由且归纳生成的数据类型。
当然，库引入了记号 ``ℕ`` 和 ``0`` 分别表示
``Nat`` 和 ``zero``。（数字被翻译为二进制表示，
但我们暂时不必担心这些细节。）

对工作中的数学家来说，"自由"意味着类型
``Nat`` 有一个元素 ``zero`` 和一个单射的后继函数
``succ``，其后继像不包含 ``zero``。
EXAMPLES: -/
-- QUOTE:
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h
-- QUOTE.

/- TEXT:
对工作中的数学家来说，"归纳地"一词意味着
自然数带有归纳证明原理
和递归定义原理。
本节将向你展示如何使用它们。

以下是阶乘函数的递归定义示例。
BOTH: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
其语法需要一些时间来适应。
注意第一行没有 ``:=``。
接下来两行为递归定义提供了
基础情形和归纳步骤。
这些等式在定义上成立，但它们也可以
通过将名称 ``fac`` 提供给 ``simp`` 或 ``rw`` 来手动使用。
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]
-- QUOTE.

/- TEXT:
阶乘函数实际上已经在 Mathlib 中定义为
``Nat.factorial``。同样，你可以通过输入
``#check Nat.factorial`` 并使用 ``ctrl-click.`` 跳转到它。
为了说明目的，我们将在示例中继续使用 ``fac``。
在 ``Nat.factorial`` 的定义之前的 ``@[simp]`` 注解指定
定义方程应被添加到化简器默认使用的
恒等式数据库中。

归纳原理说我们可以通过证明该陈述对 0 成立，
并且每当它对自然数 :math:`n` 成立时，
它对 :math:`n + 1` 也成立，来证明关于自然数的一般陈述。
下面证明中的 ``induction' n with n ih`` 行
因此导致了两个目标：
在第一个中我们需要证明 ``0 < fac 0``，
在第二个中我们添加了假设 ``ih : 0 < fac n``
并需要证明 ``0 < fac (n + 1)``。
短语 ``with n ih`` 用于为归纳假设
命名变量和假设，
你可以为它们选择任何你喜欢的名称。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
``induction'`` 策略足够聪明，可以将依赖归纳变量
的假设包含为归纳假设的一部分。
逐步执行下一个例子，看看发生了什么。
EXAMPLES: -/
-- QUOTE:
theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right
-- QUOTE.

/- TEXT:
以下例子提供了阶乘函数的粗略下界。
结果表明，从分情况证明入手更容易，
这样其余证明就从 :math:`n = 1` 的情况
开始。
看看你能否使用 ``pow_succ`` 或 ``pow_succ'``
通过归纳来完成论证。
BOTH: -/
-- QUOTE:
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul _ ih
  repeat' apply Nat.succ_le_succ
  apply zero_le

-- BOTH:
-- QUOTE.
/- TEXT:
归纳经常用于证明涉及有限和与
有限积的恒等式。
Mathlib 定义了表达式 ``Finset.sum s f``，其中
``s : Finset α`` 是类型 ``α`` 的元素的一个有限集，而
``f`` 是定义在 ``α`` 上的函数。
``f`` 的上域可以是任何支持交换、
结合加法运算并带有零元素的类型。
如果你导入 ``Algebra.BigOperators.Ring`` 并发出命令
``open BigOperators``，你可以使用更具提示性的记号
``∑ x ∈ s, f x``。当然，对于有限积有类似的运算
和记号。

我们将在下一节以及后面的章节中讨论 ``Finset`` 类型
和它支持的运算。
现在，我们只使用
``Finset.range n``，它是小于 ``n`` 的自然数
的有限集合。
BOTH: -/
section

-- QUOTE:
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

-- EXAMPLES:
#check Finset.sum s f
#check Finset.prod s f

-- BOTH:
open BigOperators
open Finset

-- EXAMPLES:
example : s.sum f = ∑ x ∈ s, f x :=
  rfl

example : s.prod f = ∏ x ∈ s, f x :=
  rfl

example : (range n).sum f = ∑ x ∈ range n, f x :=
  rfl

example : (range n).prod f = ∏ x ∈ range n, f x :=
  rfl
-- QUOTE.

/- TEXT:
事实 ``Finset.sum_range_zero`` 和 ``Finset.sum_range_succ``
提供了求直到 :math:`n` 的和的递归描述，
对乘积类似。
EXAMPLES: -/
-- QUOTE:
example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n :=
  Finset.prod_range_succ f n
-- QUOTE.

/- TEXT:
每对中的第一个恒等式在定义上成立，也就是说，
你可以用 ``rfl`` 替换证明。

以下将我们定义的阶乘函数表示为一个乘积。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n ih
  · simp [fac]
  simp [fac, ih, prod_range_succ, mul_comm]
-- QUOTE.

/- TEXT:
我们将 ``mul_comm`` 作为化简规则包含在内这一事实
值得评论。
用恒等式 ``x * y = y * x`` 进行化简似乎应该是危险的，
这会无限循环。
Lean 的化简器足够聪明，能够识别这一点，并且只在
结果项在项的某种固定但任意的排序中具有更小值的
情况下应用该规则。
下面的例子表明，使用三条规则
``mul_assoc``、``mul_comm`` 和 ``mul_left_comm`` 进行化简
能够识别出在括号位置和变量排序上
相同的乘积。
EXAMPLES: -/
-- QUOTE:
example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_comm, mul_left_comm]
-- QUOTE.

/- TEXT:
大致来说，这些规则通过将括号推到右边，
然后对两边的表达式进行重排序，直到它们
都遵循相同的规范顺序来工作。用这些规则
和相应的加法规则进行简化是一个方便的技巧。

回到求和恒等式，我们建议逐步执行以下证明：
直到并包括 :math:`n` 的自然数之和
为 :math:`n (n + 1) / 2`。
证明的第一步是清除分母。
这在形式化恒等式时通常很有用，
因为涉及除法的计算通常有附带条件。
（同样，在可能的情况下避免在自然数上使用减法也是有用的。）
EXAMPLES: -/
-- QUOTE:
theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
-- QUOTE.

/- TEXT:
我们鼓励你证明平方和的类似恒等式，
以及你在网上能找到的其他恒等式。
BOTH: -/
-- QUOTE:
theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 6, ← ih]
  ring
-- QUOTE.

-- BOTH:
end

/- TEXT:
在 Lean 的核心库中，加法和乘法本身是使用
递归定义定义的，
而它们的基本性质是使用归纳建立的。
如果你喜欢思考这样的基础性话题，
你可能会喜欢按照下面的概要
在自然数的拷贝上完成
乘法和加法的交换律、结合律
以及乘法对加法的分配律的证明。
注意我们可以对 ``MyNat`` 使用 ``induction`` 策略；
Lean 足够聪明，知道要使用
相关的归纳原理（当然，与 ``Nat`` 的归纳原理
相同）。

我们从加法的交换律开始。
一个好的经验法则是，因为加法和乘法
是通过对第二个参数进行递归定义的，
通常对出现在该位置的变量
进行归纳证明是有利的。
在结合律的证明中
决定使用哪个变量有点棘手。

在没有通常的零、一、加法和乘法记号的情况下
书写可能会令人困惑。
我们将在以后学习如何定义这样的记号。
在命名空间 ``MyNat`` 中工作意味着我们可以写
``zero`` 和 ``succ`` 而不是 ``MyNat.zero`` 和 ``MyNat.succ``，
并且这些名字的解释优先于
其他解释。
在命名空间之外，例如下面定义的 ``add`` 的全名
是 ``MyNat.add``。

如果你发现你*真的*喜欢这类事情，尝试定义
截断减法和幂运算，并证明它们的一些
性质。
记住截断减法在零处截断。
要定义它，定义一个前驱函数 ``pred`` 是有用的，
它从任何非零数减一并保持零不变。
函数 ``pred`` 可以通过简单的递归实例来定义。
BOTH: -/
-- QUOTE:
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, ih]
  rfl

-- BOTH:
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, mul, mul, ih, add_assoc]

-- BOTH:
theorem zero_mul (n : MyNat) : mul zero n = zero := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, ih]
  rfl

-- BOTH:
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add]
  rfl

-- BOTH:
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rw [zero_mul]
    rfl
  rw [mul, ih, succ_mul]

-- BOTH:
end MyNat
-- QUOTE.
