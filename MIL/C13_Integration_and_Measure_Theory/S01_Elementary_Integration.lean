import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convolution

open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
.. index:: integration

.. _elementary_integration:

初等积分
--------

我们首先关注 ``ℝ`` 上有限区间上的函数积分。我们可以积分初等函数。
EXAMPLES: -/
-- QUOTE:
open MeasureTheory intervalIntegral

open Interval
-- 这引入了记号 `[[a, b]]`，表示从 `min a b` 到 `max a b` 的区间

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
-- QUOTE.

/- TEXT:
微积分基本定理将积分与微分联系起来。
下面我们给出该定理两个部分的简化版本。第一部分
说明积分提供了微分的逆运算，第二部分
说明如何计算导数的积分。
（这两部分联系非常紧密，但它们的最优版本（此处未展示）并不等价。）
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- QUOTE.

/- TEXT:
卷积在 Mathlib 中也被定义了，并且其基本性质已被证明。
EXAMPLES: -/
-- QUOTE:
open Convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl
-- QUOTE.
