-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

/- TEXT:
.. _sequences_and_convergence:

数列与收敛
-------------------------

我们现在已经掌握了足够的技能来做一些真正的数学。
在 Lean 中，我们可以将实数序列 :math:`s_0, s_1, s_2, \ldots`
表示为一个函数 ``s : ℕ → ℝ``。
这样一个序列被称为*收敛*到数 :math:`a`，如果对于每个
:math:`\varepsilon > 0`，存在某个点，在该点之后序列
保持在 :math:`a` 的 :math:`\varepsilon` 范围内，
即存在一个数 :math:`N`，使得对于每个
:math:`n \ge N`，有 :math:`| s_n - a | < \varepsilon`。
在 Lean 中，我们可以这样表述：
BOTH: -/
-- QUOTE:
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

/- TEXT:
记号 ``∀ ε > 0, ...`` 是
``∀ ε, ε > 0 → ...`` 的方便缩写，类似地，
``∀ n ≥ N, ...`` 是 ``∀ n, n ≥ N →  ...`` 的缩写。
同时记住 ``ε > 0`` 被定义为 ``0 < ε``，
而 ``n ≥ N`` 被定义为 ``N ≤ n``。

.. index:: extensionality, ext, tactics ; ext

在本节中，我们将建立收敛的一些性质。
但首先，我们将讨论三个处理等式的策略，
它们将会很有用。
第一个是 ``ext`` 策略，
它为我们提供了一种证明两个函数相等的方法。
设 :math:`f(x) = x + 1` 和 :math:`g(x) = 1 + x`
是从实数到实数的函数。
那么，当然，:math:`f = g`，因为它们对每个 :math:`x`
都返回相同的值。
``ext`` 策略使我们能够通过证明
函数在它们参数的所有取值处
具有相同的值来证明函数之间的等式。
TEXT. -/
-- QUOTE:
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring
-- QUOTE.

/- TEXT:
.. index:: congr, tactics ; congr

我们稍后会看到 ``ext`` 实际上是更一般的，而且还可以
指定出现的变量的名称。
例如，你可以尝试在上面的证明中将 ``ext`` 替换为 ``ext u v``。
第二个策略，``congr`` 策略，
允许我们通过调和不同的部分
来证明两个表达式之间的等式：
TEXT. -/
-- QUOTE:
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring
-- QUOTE.

/- TEXT:
这里 ``congr`` 策略剥去了每一边的 ``abs``，
留下 ``a = a - b + b`` 需要证明。

.. index:: convert, tactics ; convert

最后，``convert`` 策略用于当定理的结论不完全匹配时，
将定理应用于目标。
例如，假设我们想从 ``1 < a`` 证明 ``a < a * a``。
库中的一个定理 ``mul_lt_mul_iff_left₀``
将使我们能够证明 ``1 * a < a * a``。
一种可能性是反向工作，重写目标
使其具有那种形式。
而 ``convert`` 策略让我们可以直接应用定理，
并留下证明使目标匹配所需等式的任务。
TEXT. -/
-- QUOTE:
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
-- QUOTE.

/- TEXT:
这个例子说明了另一个有用的技巧：当我们应用一个
带有下划线的表达式，
而 Lean 无法自动为我们填充它时，
它只是将其留作另一个目标。

以下证明了任何常数序列 :math:`a, a, a, \ldots`
收敛。
BOTH: -/
-- QUOTE:
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
-- QUOTE.

/- TEXT:
.. TODO: reference to the simplifier

Lean 有一个策略 ``simp``，它通常可以为你省去
手动执行诸如 ``rw [sub_self, abs_zero]`` 这类步骤的麻烦。
我们很快会告诉你更多关于它的信息。

对于一个更有趣的定理，让我们证明如果 ``s``
收敛到 ``a`` 且 ``t`` 收敛到 ``b``，那么
``fun n ↦ s n + t n`` 收敛到 ``a + b``。
在开始编写形式化证明之前，心中有一个清晰的纸笔
证明是有帮助的。
给定大于 ``0`` 的 ``ε``，
思路是使用假设获得一个 ``Ns``，
使得在该点之后，``s`` 在 ``a`` 的 ``ε / 2``
范围内，
以及一个 ``Nt``，使得在该点之后，``t`` 在
``b`` 的 ``ε / 2`` 范围内。
那么，每当 ``n`` 大于或等于
``Ns`` 和 ``Nt`` 中的最大值时，
序列 ``fun n ↦ s n + t n`` 应该在 ``a + b`` 的 ``ε``
范围内。
以下例子开始实施这个策略。
看看你能否完成它。
TEXT. -/
-- QUOTE:
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- 此行不是必需的，但可以使目标更清晰一些。
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_addαα {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := (abs_add_le _ _)
    _ < ε / 2 + ε / 2 := (add_lt_add (hs n ngeNs) (ht n ngeNt))
    _ = ε := by norm_num

/- TEXT:
作为提示，你可以使用 ``le_of_max_le_left`` 和 ``le_of_max_le_right``，
而 ``norm_num`` 可以证明 ``ε / 2 + ε / 2 = ε``。
另外，使用 ``congr`` 策略来
证明 ``|s n + t n - (a + b)|`` 等于
``|(s n - a) + (t n - b)|`` 是有帮助的，
因为这样你就可以使用三角不等式。
注意我们将所有变量 ``s``、``t``、``a`` 和 ``b``
标记为隐式，因为它们可以从假设中推断出来。

将乘法代替加法来证明同样的定理
是棘手的。
我们将通过首先证明一些辅助命题来达到这个目标。
看看你能否也完成下一个证明，
它证明了如果 ``s`` 收敛到 ``a``，
那么 ``fun n ↦ c * s n`` 收敛到 ``c * a``。
根据 ``c`` 是否等于零
来分情况讨论是有帮助的。
我们已经处理了零的情况，
留给你在额外的假设 ``c`` 非零
的情况下证明该结果。
TEXT. -/
-- QUOTE:
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_mul_constαα {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := (mul_lt_mul_of_pos_left (hs n ngt) acpos)
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm

/- TEXT:
下一个定理也是独立有趣的：
它证明了一个收敛序列的绝对值
最终是有界的。
我们已经为你开了个头；看看你能否完成它。
TEXT. -/
-- QUOTE:
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem exists_abs_le_of_convergesToαα {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |s n - a + a| := by
      congr
      abel
    _ ≤ |s n - a| + |a| := (abs_add_le _ _)
    _ < |a| + 1 := by linarith [h n ngt]

/- TEXT:
事实上，该定理可以被加强为断言
存在一个对 ``n`` 的所有值都成立的界 ``b``。
但这个版本对我们的目的来说已经足够强了，
我们将在本节末尾看到它
在更一般的情况下也成立。

下一个引理是辅助性的：我们证明如果
``s`` 收敛到 ``a`` 且 ``t`` 收敛到 ``0``，
那么 ``fun n ↦ s n * t n`` 收敛到 ``0``。
为此，我们使用前面的定理找到一个 ``B``，
它在某点 ``N₀`` 之后界定了 ``s``。
看看你能否理解我们概述的策略
并完成证明。
TEXT. -/
-- QUOTE:
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

/- TEXT:
如果你已经走到了这一步，恭喜！
我们现在已经接近我们的定理了。
以下证明完成了它。
TEXT. -/
-- QUOTE:
-- BOTH:
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
-- QUOTE.

/- TEXT:
另一个有挑战性的练习是，
尝试填写下面极限唯一性的证明概要。
（如果你有勇气，
可以删除证明概要并尝试从头证明它。）
TEXT. -/
-- QUOTE:
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_uniqueαα {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add_le _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this

/- TEXT:
我们以观察到我们的证明可以推广来结束本节。
例如，我们使用自然数的唯一
性质是它们的结构带有具有 ``min`` 和 ``max`` 的
偏序。
你可以检查，如果你用任意线性序 ``α``
替换所有地方的 ``ℕ``，一切仍然有效：
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

end

/- TEXT:
在 :numref:`filters` 中，我们将看到 Mathlib 有
以更一般的方式处理收敛的机制，
不仅抽象掉定义域和陪域
的特定特征，
还抽象掉不同类型的收敛。
TEXT. -/
