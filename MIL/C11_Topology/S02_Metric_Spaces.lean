import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

/- TEXT:
.. index:: metric space

.. _metric_spaces:

度量空间
--------------

上一节的例子侧重于实数序列。在本节中，我们将稍微提高一下普遍性，关注
度量空间。度量空间是一个类型 ``X``，配备了一个距离函数 ``dist : X → X → ℝ``，它是
函数 ``fun x y ↦ |x - y|`` 从 ``X = ℝ`` 的情况的推广。

引入这样一个空间很容易，我们将检查距离函数所需的所有性质。
BOTH: -/
-- QUOTE:
variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)
-- QUOTE.

/- TEXT:
注意，我们还有距离可以是无穷的，或者 ``dist a b`` 可以为零但 ``a = b`` 不成立，或两者兼有的变体。
它们分别称为 ``EMetricSpace``、``PseudoMetricSpace`` 和 ``PseudoEMetricSpace``（这里 "e" 代表 "extended"）。

BOTH: -/
-- 注意，接下来三行没有被引用，它们的目的是确保在我们关注其他地方时这些东西不会被重命名。
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

/- TEXT:
注意，我们从 ``ℝ`` 到度量空间的旅程跳过了赋范空间的特例，后者也需要线性代数，
并将在微积分章节中作为一部分加以解释。

收敛与连续性
^^^^^^^^^^^^^^^^^^^^^^^^^^

使用距离函数，我们已经可以定义度量空间之间的收敛序列和连续函数。
它们实际上在下一节涵盖的更一般背景中定义，
但我们有引理用距离重新表述这个定义。
BOTH: -/
-- QUOTE:
example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff
-- QUOTE.

/- TEXT:
.. index:: continuity, tactics ; continuity


很多引理都有一些连续性假设，因此我们最终要证明很多连续性结果，并且有一个
``continuity`` 策略专门用于此任务。让我们证明一个在下面的练习中需要的连续性陈述。
注意，Lean 知道如何将两个度量空间的积视为度量空间，因此
考虑从 ``X × X`` 到 ``ℝ`` 的连续函数是有意义的。
特别地，距离函数的（非柯里化版本）就是这样一个函数。

BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity
-- QUOTE.

/- TEXT:
这个策略有点慢，因此知道如何手工完成也是有用的。
我们首先需要使用 ``fun p : X × X ↦ f p.1`` 是连续的，因为它
是 ``f``（由假设 ``hf`` 是连续的）与投影 ``prod.fst``（其连续性
是引理 ``continuous_fst`` 的内容）的复合。复合性质是 ``Continuous.comp``，它在
``Continuous`` 命名空间中，因此我们可以使用点记号将
``Continuous.comp hf continuous_fst`` 压缩为 ``hf.comp continuous_fst``，后者实际上更可读，
因为它确实读作将我们的假设和我们的引理复合。
我们可以对第二个分量做同样的处理，得到 ``fun p : X × X ↦ f p.2`` 的连续性。然后我们
使用 ``Continuous.prod_mk`` 将这两个连续性组合起来，得到
``(hf.comp continuous_fst).prod_mk (hf.comp continuous_snd) : Continuous (fun p : X × X ↦ (f p.1, f p.2))``
并再复合一次来得到我们的完整证明。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))
-- QUOTE.

/- TEXT:
即使像上面那样大量使用点记号，``Continuous.prod_mk`` 和 ``continuous_dist`` 通过 ``Continuous.comp`` 的组合
也显得笨拙。一个更严重的问题是，这个漂亮的证明需要大量的
规划。Lean 接受上面的证明项是因为它是一个完整的项，证明了一个与我们的目标
按定义等价的陈述，需要展开的关键定义是函数的复合。
实际上，我们的目标函数 ``fun p : X × X ↦ dist (f p.1) (f p.2)`` 并没有表现为一个复合。
我们提供的证明项证明了 ``dist ∘ (fun p : X × X ↦ (f p.1, f p.2))`` 的连续性，而后者
恰好与我们的目标函数按定义相等。但如果我们尝试使用策略逐步构建这个证明，
从 ``apply continuous_dist.comp`` 开始，那么 Lean 的 elaborator 将无法识别
复合并拒绝应用这个引理。当涉及类型的积时，它在这方面尤其糟糕。

这里更好的应用引理是
``Continuous.dist {f g : X → Y} : Continuous f → Continuous g → Continuous (fun x ↦ dist (f x) (g x))``，
它对 Lean 的 elaborator 更友好，并且在直接提供完整
证明项时也给出了更短的证明，这可以从上述陈述的以下两个新证明中看出：
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)
-- QUOTE.

/- TEXT:
注意，在没有复合带来的 elaborator 问题的情况下，另一种压缩
我们证明的方法是使用 ``Continuous.prod_map``，它有时很有用，并给出
替代证明项 ``continuous_dist.comp (hf.prod_map hf)``，输入起来甚至更短。

由于在对 elaborator 更友好的版本和输入更短的版本之间做出选择令人遗憾，
让我们用 ``Continuous.fst'`` 所提供的最后一点压缩来结束这个讨论，
它允许将 ``hf.comp continuous_fst`` 压缩为 ``hf.fst'``（``snd`` 同理），
并得到我们最终的证明，此时已近乎难以辨认。

BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'
-- QUOTE.

/- TEXT:
现在轮到你来证明一些连续性引理了。在尝试 continuity 策略之后，你将需要
``Continuous.add``、``continuous_pow`` 和 ``continuous_id`` 来手工完成。

BOTH: -/
-- QUOTE:
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  hf.comp <| (continuous_pow 2).add continuous_id

-- QUOTE.

/- TEXT:
到目前为止，我们将连续性视为全局概念，但也可以定义在一点处的连续性。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff
-- QUOTE.

/- TEXT:

球、开集与闭集
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

一旦有了距离函数，最重要的几何定义是（开）球和闭球。

BOTH: -/
-- QUOTE:
variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl
-- QUOTE.

/- TEXT:
注意这里 `r` 是任意实数，没有符号限制。当然，有些陈述确实需要半径条件。
BOTH: -/
-- QUOTE:
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr
-- QUOTE.

/- TEXT:
有了球之后，我们可以定义开集。它们实际上在下一节涵盖的更一般背景中定义，
但我们有引理用球重新表述这个定义。

BOTH: -/
-- QUOTE:
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff
-- QUOTE.

/- TEXT:
然后闭集是其补集为开集的集合。它们的重要性质是对极限封闭。一个集合的闭包是包含它的最小闭集。
BOTH: -/
-- QUOTE:
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff
-- QUOTE.

/- TEXT:
完成下一个练习时不要使用 `mem_closure_iff_seq_limit`。
BOTH: -/
-- QUOTE:
example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  refine ⟨u N, hs _, ?_⟩
  rw [dist_comm]
  exact hN N le_rfl

-- QUOTE.

/- TEXT:

回忆一下滤子部分中邻域滤子在 Mathlib 中扮演着重要角色。
在度量空间语境中，关键点是球为这些滤子提供了基。
这里的主要引理是 ``Metric.nhds_basis_ball`` 和 ``Metric.nhds_basis_closedBall``，
它们声称这对具有正半径的开球和闭球成立。中心点是隐式
参数，因此我们可以像下面的例子一样调用 ``Filter.HasBasis.mem_iff``。

BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff
-- QUOTE.

/- TEXT:

紧性
^^^^^^^^^^^

紧性是一个重要的拓扑概念。它区分度量空间的子集中那些
享有与实数中的区间相比其他区间所具有的同类性质的子集：

* 取值在紧集中的任何序列都有在该集合中收敛的子列。
* 非空紧集上的任何取实数值的连续函数是有界的，并且
  在某处达到其界（这称为极值定理）。
* 紧集是闭集。

让我们首先验证实数中的单位闭区间确实是一个紧集，然后检查上述
关于一般度量空间中紧集的断言。在第二个陈述中，我们只需要
在给定集合上的连续性，因此我们将使用 ``ContinuousOn`` 而不是 ``Continuous``，并且
我们将为最小值和最大值分别给出陈述。当然，所有这些结果
都是从更一般的版本推导出来的，其中一些将在后面的章节中讨论。

BOTH: -/
-- QUOTE:
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
-- QUOTE.

/- TEXT:

我们也可以使用一个额外的 ``Prop`` 值类型类来指定度量空间是全局紧的：

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
-- QUOTE.

/- TEXT:

在紧度量空间中，任何闭集都是紧的，这是 ``IsClosed.isCompact``。

BOTH: -/
#check IsCompact.isClosed

/- TEXT:
一致连续函数
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

现在我们转向度量空间上的一致性质：一致连续函数、Cauchy 列和完备性。
同样，这些是在更一般的语境中定义的，但我们在度量命名空间中有引理来获取它们的初等定义。
我们从一致连续性开始。

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff
-- QUOTE.

/- TEXT:
为了练习操作所有这些定义，我们将证明从紧度量空间到度量空间的连续
函数是一致连续的
（我们将在后面的章节中看到一个更一般的版本）。

我们首先给出一个非正式的草图。设 ``f : X → Y`` 是从
紧度量空间到度量空间的连续函数。
我们固定 ``ε > 0`` 并开始寻找某个 ``δ``。

设 ``φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)`` 并设 ``K := { p : X × X | ε ≤ φ p }``。
观察到 ``φ`` 是连续的，因为 ``f`` 和距离是连续的。
而 ``K`` 显然是闭的（使用 ``isClosed_le``），因此是紧的，因为 ``X`` 是紧的。

然后我们使用 ``eq_empty_or_nonempty`` 讨论两种可能性。
如果 ``K`` 是空的，那么我们显然完成了（例如我们可以设 ``δ = 1``）。
因此假设 ``K`` 非空，并使用极值定理选择 ``(x₀, x₁)`` 达到 ``K`` 上
距离函数的下确界。然后我们可以设 ``δ = dist x₀ x₁`` 并检查一切成立。

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    simpa [K] using this
  · rcases K_cpct.exists_isMinOn hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · change _ < _
      rw [dist_pos]
      intro h
      have : ε ≤ 0 := by simpa [K, φ, *] using xx_in
      linarith
    · intro x x'
      contrapose!
      intro (hxx' : (x, x') ∈ K)
      exact H hxx'

-- QUOTE.

/- TEXT:
完备性
^^^^^^^^^^^^

度量空间中的 Cauchy 列是其项彼此越来越接近的序列。
有几种等价的方式来陈述这个想法。
特别地，收敛序列是 Cauchy 列。逆命题仅对所谓的*完备*
空间成立。


BOTH: -/
-- QUOTE:
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu
-- QUOTE.

/- TEXT:

我们将通过证明一个方便的判据来练习使用这个定义，该判据是
Mathlib 中出现的一个判据的特例。这也是在几何语境中练习使用大求和的好机会。
除了滤子部分的解释外，你大概还需要
``tendsto_pow_atTop_nhds_zero_of_lt_one``、``Tendsto.mul`` 和 ``dist_le_range_sum_dist``。
BOTH: -/
open BigOperators

open Finset

-- QUOTE:
-- EXAMPLES:
theorem cauchySeq_of_le_geometric_two'αα {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i  ∈ range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i  ∈ range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i  ∈ range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry

-- QUOTE.

-- SOLUTIONS:
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun N : ℕ ↦ (1 / 2 ^ N * 2 : ℝ)) atTop (𝓝 0) := by
      rw [← zero_mul (2 : ℝ)]
      apply Tendsto.mul
      simp_rw [← one_div_pow (2 : ℝ)]
      apply tendsto_pow_atTop_nhds_zero_of_lt_one <;> linarith
      exact tendsto_const_nhds
    rcases(atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, _, hN⟩
    exact ⟨N, by simpa using (hN N self_mem_Ici).2⟩
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by rw [dist_comm, add_zero]
    _ ≤ ∑ i  ∈ range k, dist (u (N + i)) (u (N + (i + 1))) :=
      (dist_le_range_sum_dist (fun i ↦ u (N + i)) k)
    _ ≤ ∑ i  ∈ range k, (1 / 2 : ℝ) ^ (N + i) := (sum_le_sum fun i _ ↦ hu <| N + i)
    _ = 1 / 2 ^ N * ∑ i  ∈ range k, (1 / 2 : ℝ) ^ i := by simp_rw [← one_div_pow, pow_add, ← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 :=
      (mul_le_mul_of_nonneg_left (sum_geometric_two_le _)
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) _)))
    _ < ε := hN


/- TEXT:

我们准备好了迎接本节的最终 Boss：完备度量空间的 Baire 定理！
下面的证明框架展示了有趣的技巧。它使用了 ``choose`` 策略的感叹号
变体（你应该尝试去掉这个感叹号），并展示了如何在证明
中间使用 ``Nat.rec_on`` 归纳地定义某些东西。

BOTH: -/
-- QUOTE:
open Metric

-- EXAMPLES:
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- 将稠密性假设转化为两个函数 `center` 和 `radius`，它们将
    任何 n, x, δ, δpos 关联到一个中心和正半径，使得
    `closedBall center radius` 既包含在 `f n` 中又包含在 `closedBall x δ` 中。
    我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保稍后得到 Cauchy 序列。 -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` 是正的。我们需要在 `x` 周围半径为 `ε` 的球中找到一个属于所有 `f n` 的点。
    为此，我们归纳地构造一个序列 `F n = (c n, r n)`，使得闭球
    `closedBall (c n) (r n)` 包含在前一个球中且在 `f n` 中，并且使得
    `r n` 足够小以确保 `c n` 是 Cauchy 序列。然后 `c n` 收敛到一个
    属于所有 `f n` 的极限。 -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是 Cauchy 列，它收敛到一个极限 `y`。
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- 这个点 `y` 将是我们所需的点。我们将检查它属于所有
  -- `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦ pow_pos (by linarith) n
  /- 将稠密性假设转化为两个函数 `center` 和 `radius`，它们将
    任何 n, x, δ, δpos 关联到一个中心和正半径，使得
    `closedBall center radius` 既包含在 `f n` 中又包含在 `closedBall x δ` 中。
    我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保稍后得到 Cauchy 序列。 -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases Metric.mem_closure_iff.1 this (δ / 2) (half_pos δpos) with ⟨y, ys, xy⟩
    rw [dist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedBall y r ⊆ f n :=
      nhds_basis_closedBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine ⟨y, min (min (δ / 2) r) (B (n + 1)), ?_, ?_, fun z hz ↦ ⟨?_, ?_⟩⟩
    show 0 < min (min (δ / 2) r) (B (n + 1))
    exact lt_min (lt_min (half_pos δpos) rpos) (Bpos (n + 1))
    show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
    exact min_le_right _ _
    show z ∈ closedBall x δ
    exact
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := (add_le_add hz xy.le)
        _ ≤ δ / 2 + δ / 2 := (add_le_add_left ((min_le_left _ _).trans (min_le_left _ _)) _)
        _ = δ := add_halves δ

    show z ∈ f n
    exact
      hr
        (calc
          dist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
          _ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
          )
  choose! center radius Hpos HB Hball using this
  refine fun x ↦ (mem_closure_iff_nhds_basis nhds_basis_closedBall).2 fun ε εpos ↦ ?_
  /- `ε` 是正的。我们需要在 `x` 周围半径为 `ε` 的球中找到一个属于所有
    `f n` 的点。为此，我们归纳地构造一个序列 `F n = (c n, r n)`，使得闭球
    `closedBall (c n) (r n)` 包含在前一个球中且在 `f n` 中，并且使得
    `r n` 足够小以确保 `c n` 是 Cauchy 序列。然后 `c n` 收敛到一个
    属于所有 `f n` 的极限。 -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    exact min_le_right _ _
    exact HB n (c n) (r n) (rpos n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := fun n ↦
    Hball n (c n) (r n) (rpos n)
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [dist_comm]
    have A : c (n + 1) ∈ closedBall (c (n + 1)) (r (n + 1)) :=
      mem_closedBall_self (rpos <| n + 1).le
    have I :=
      calc
        closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
          (incl n).trans Set.inter_subset_left
        _ ⊆ closedBall (c n) (B n) := closedBall_subset_closedBall (rB n)

    exact I A
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是 Cauchy 列，它收敛到一个极限 `y`。
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- 这个点 `y` 将是我们所需的点。我们将检查它属于所有
  -- `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine Nat.le_induction ?_ fun m hnm h ↦ ?_
    · exact Subset.rfl
    · exact (incl m).trans (Set.inter_subset_left.trans h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    refine isClosed_closedBall.mem_of_tendsto ylim ?_
    refine (Filter.eventually_ge_atTop n).mono fun m hm ↦ ?_
    exact I n m hm (mem_closedBall_self (rpos _).le)
  constructor
  · suffices ∀ n, y ∈ f n by rwa [Set.mem_iInter]
    intro n
    have : closedBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) Set.inter_subset_right
    exact this (yball (n + 1))
  calc
    dist y x ≤ r 0 := yball 0
    _ ≤ ε := min_le_left _ _
