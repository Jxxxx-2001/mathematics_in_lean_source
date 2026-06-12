import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

open Topology Filter ENNReal

open MeasureTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/- TEXT:
.. _integration:

积分
----

现在有了可测空间和测度，我们就可以考虑积分了。
如上所述，Mathlib 使用非常一般的积分概念，允许目标空间为任意 Banach 空间。
和往常一样，我们不希望记号带着假设到处走，所以我们这样定义积分：
如果所讨论的函数不可积，则积分为零。
大多数与积分相关的引理都有可积性假设。
EXAMPLES: -/
-- QUOTE:
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
-- QUOTE.

/- TEXT:
作为各种约定之间复杂交互的一个例子，我们来看看如何积分常值函数。
回忆一下，测度 ``μ`` 的值在 ``ℝ≥0∞`` 中，即扩展非负实数类型。
有一个函数 ``ENNReal.toReal : ℝ≥0∞ → ℝ``，它将无穷远点 ``⊤`` 映射为零。
对任意 ``s : Set α``，如果 ``μ s = ⊤``，那么非零常值函数在 ``s`` 上不可积。
在这种情况下，根据定义它们的积分为零，``(μ s).toReal`` 也是如此。
因此在所有情况下，我们有以下引理。
EXAMPLES: -/
-- QUOTE:
example {s : Set α} (c : E) : ∫ _ in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c
-- QUOTE.

/- TEXT:
我们快速说明一下如何查阅积分理论中最重要的定理，首先
从控制收敛定理开始。Mathlib 中有多个版本，
这里我们仅展示最基本的版本。
EXAMPLES: -/
-- QUOTE:
open Filter

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim
-- QUOTE.

/- TEXT:
然后是乘积类型上积分的 Fubini 定理。
EXAMPLES: -/
-- QUOTE:
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
-- QUOTE.

end

/- TEXT:
卷积有一个非常一般的版本，适用于任意连续双线性形式。
EXAMPLES: -/
section

-- QUOTE:
open Convolution

-- EXAMPLES:
variable {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedSpace ℝ F] [CompleteSpace F]
  [Sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) :
    f ⋆[L, μ] g = fun x ↦ ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
-- QUOTE.

end

/- TEXT:
最后，Mathlib 有一个非常一般的变量替换公式。
在下面的陈述中，``BorelSpace E`` 意味着
``E`` 上的 :math:`\sigma`-代数由 ``E`` 的开集生成，
而 ``IsAddHaarMeasure μ`` 意味着测度 ``μ`` 是左不变的、
对紧集赋予有限质量、对开集赋予正质量。
EXAMPLES: -/
-- QUOTE:
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {f : E → E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf : ∀ x : E, x ∈ s → HasFDerivWithinAt f (f' x) s x) (h_inj : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
  integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g
-- QUOTE.
