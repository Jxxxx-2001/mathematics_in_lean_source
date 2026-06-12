import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

/- TEXT:
.. index:: measure theory

.. _measure_theory:

测度论
------

Mathlib 中积分的一般背景是测度论。即使是上一节的初等积分，实际上也是 Bochner 积分。
Bochner 积分是 Lebesgue 积分的推广，其目标空间可以是任意 Banach 空间，而不必是有限维的。

测度论展开的第一个组成部分是集合的 :math:`\sigma`-代数的概念，这些集合称为
*可测* 集。
类型类 ``MeasurableSpace`` 用于为类型装备这样的结构。
集合 ``empty`` 和 ``univ`` 是可测的，
可测集的补集是可测的，
可测集的可数并或可数交也是可测的。
请注意，这些公理是冗余的；如果你 ``#print MeasurableSpace``，
你会看到 Mathlib 实际使用的公理。
如下面的例子所示，可数性假设可以使用
``Encodable`` 类型类来表达。
BOTH: -/
-- QUOTE:
variable {α : Type*} [MeasurableSpace α]

-- EXAMPLES:
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

-- BOTH:
variable {ι : Type*} [Encodable ι]

-- EXAMPLES:
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
-- QUOTE.

/- TEXT:
一旦一个类型是可测的，我们就可以对其进行测量。在纸面上，装备了 :math:`\sigma`-代数的集合
（或类型）上的测度是一个从可测集到扩展非负实数的函数，
它在可数不交并上是可加的。
在 Mathlib 中，我们不想每次将测度应用于一个集合时都带着可测性假设。
因此，我们将测度扩展到任意集合 ``s``，定义为其超集的可测集的测度的下确界。
当然，许多引理仍然需要可测性假设，但不是全部。
BOTH: -/
-- QUOTE:
open MeasureTheory Function
variable {μ : Measure α}

-- EXAMPLES:
example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis
-- QUOTE.

/- TEXT:
一旦一个类型关联了测度，我们说一个性质 ``P`` *几乎处处* 成立，如果该性质不成立的元素组成的集合
测度为零。
几乎处处成立的性质的全体构成一个滤子，
但 Mathlib 引入了特殊记号来表示一个性质几乎处处成立。
EXAMPLES: -/
-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl
-- QUOTE.
