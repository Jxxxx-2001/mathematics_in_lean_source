import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable section

/- TEXT:
.. index:: elementary calculus

.. _elementary_differential_calculus:

初等微分学
----------

设 ``f`` 是一个从实数到实数的函数。谈论 ``f`` 在单点处的导数与谈论导函数是有区别的。
在 Mathlib 中，第一个概念表示如下。
EXAMPLES: -/
-- QUOTE:
open Real

/-- sin 函数在 0 处的导数为 1。-/
example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0
-- QUOTE.

/- TEXT:
我们也可以通过写 ``DifferentiableAt ℝ`` 来表达 ``f`` 在一点处可微，而不指定其在该点的导数。
我们显式指定 ``ℝ`` 是因为在稍微更一般的上下文中，当讨论从 ``ℂ`` 到 ``ℂ`` 的函数时，
我们希望能够区分实数意义下的可微与复数导数意义下的可微。
EXAMPLES: -/
-- QUOTE:
example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt
-- QUOTE.

/- TEXT:
每次引用导数时都要提供可微性证明会很不方便。
因此 Mathlib 提供了一个函数 ``deriv f : ℝ → ℝ``，它对任意函数 ``f : ℝ → ℝ`` 有定义，
但在 ``f`` 不可微的任何点处其值被定义为 ``0``。
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h
-- QUOTE.

/- TEXT:
当然，关于 ``deriv`` 有许多引理确实需要可微性假设。
例如，你应该思考一下，在没有可微性假设的情况下，下一个引理的反例是什么。
EXAMPLES: -/
-- QUOTE:
example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- QUOTE.

/- TEXT:
然而有趣的是，有些命题可以利用 ``deriv`` 在函数不可微时默认取零这一事实来避免可微性假设。
因此，要理解下面的命题就需要知道 ``deriv`` 的精确定义。
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero
-- QUOTE.

/- TEXT:
我们甚至可以不附加任何可微性假设来陈述罗尔定理，这似乎更加奇怪。
EXAMPLES: -/
-- QUOTE:
open Set

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI
-- QUOTE.

/- TEXT:
当然，这个技巧对一般的均值定理不适用。
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'
-- QUOTE.

/- TEXT:
Lean 可以使用 ``simp`` 策略自动计算一些简单的导数。
EXAMPLES: -/
-- QUOTE:
example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp
-- QUOTE.
