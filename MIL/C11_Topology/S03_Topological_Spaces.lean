import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter Topology

/- TEXT:
.. index:: topological space

.. _topological_spaces:

拓扑空间
------------------

基础
^^^^^^^^^^^^

现在我们提升普遍性，引入拓扑空间。我们将回顾定义
拓扑空间的两种主要方式，然后解释为什么拓扑空间的范畴比
度量空间的范畴表现得好得多。注意，我们在这里不会使用 Mathlib 的范畴论，只是
有一个略微范畴化的观点。

考虑从度量空间过渡到拓扑空间的第一种方式是，我们只
记住开集的概念（或等价地，闭集的概念）。从这个观点看，
拓扑空间是一个配备了一族称为开集的集合的类型。这一族集合
必须满足下面给出的一些公理（这一族集合略有冗余，但我们将忽略这一点）。
BOTH: -/
-- QUOTE:
section
variable {X : Type*} [TopologicalSpace X]

example : IsOpen (univ : Set X) :=
  isOpen_univ

example : IsOpen (∅ : Set X) :=
  isOpen_empty

example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs
-- QUOTE.

/- TEXT:

闭集然后被定义为补集是开集的集合。拓扑空间之间的一个函数
是（全局）连续的，如果所有开集的原像都是开集。
BOTH: -/
-- QUOTE:
variable {Y : Type*} [TopologicalSpace Y]

example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
-- QUOTE.

/- TEXT:
有了这个定义，我们已经看到，与度量空间相比，拓扑空间只记住
足够讨论连续函数的信息：一个类型上的两种拓扑结构是
相同的当且仅当它们具有相同的连续函数（实际上，恒等函数将在
两个方向上连续当且仅当两种结构具有相同的开集）。

然而，一旦我们转向在一点处的连续性，我们就看到了基于
开集的方法的局限性。在 Mathlib 中，我们经常将拓扑空间视为配备了
附加在每个点 ``x`` 上的邻域滤子 ``𝓝 x`` 的类型（相应的函数
``X → Filter X`` 满足下面进一步解释的某种条件）。回忆一下滤子部分中，
这些工具扮演着两个相关的角色。首先，``𝓝 x`` 被看作 ``X`` 中
接近 ``x`` 的点的广义集合。然后它被看作提供了一种方式，对任何谓词 ``P : X → Prop``，
说这个谓词对足够接近 ``x`` 的点成立。让我们陈述
``f : X → Y`` 在 ``x`` 处连续。纯滤子的方式是，说 ``f`` 下
接近 ``x`` 的点的广义集合的直接像包含在
接近 ``f x`` 的点的广义集合中。回忆一下，这写作 ``map f (𝓝 x) ≤ 𝓝 (f x)``
或 ``Tendsto f (𝓝 x) (𝓝 (f x))``。

BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl
-- QUOTE.

/- TEXT:
也可以同时使用视为普通集合的邻域和视为广义集合的邻域滤子来表述：
"对于 ``f x`` 的任何邻域 ``U``，所有接近 ``x`` 的点
都被发送到 ``U``"。注意，证明同样是 ``Iff.rfl``，这种观点按定义
等价于前一种观点。

BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl
-- QUOTE.

/- TEXT:
现在我们解释如何从一种观点过渡到另一种观点。用开集的语言，我们可以
简单地将 ``𝓝 x`` 的成员定义为包含一个含有 ``x`` 的开集的集合。


BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff
-- QUOTE.

/- TEXT:
为了走向另一个方向，我们需要讨论 ``𝓝 : X → Filter X`` 必须满足的
条件，才能成为一个拓扑的邻域函数。

第一个约束是，``𝓝 x`` 作为广义集合，包含集合 ``{x}``（视为广义集合
``pure x``）（解释这个奇怪的名字会离题太远，所以我们暂时接受它）。
另一种说法是，如果某个谓词对接近 ``x`` 的点成立，那么它在 ``x`` 处也成立。

BOTH: -/
-- QUOTE:
example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds
-- QUOTE.

/- TEXT:
然后一个更微妙的要求是，对于任何谓词 ``P : X → Prop`` 和任何 ``x``，如果 ``P y`` 对接近
``x`` 的 ``y`` 成立，那么对于接近 ``x`` 的 ``y`` 和接近 ``y`` 的 ``z``，``P z`` 也成立。更精确地说，我们有：
BOTH: -/
-- QUOTE:
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h
-- QUOTE.

/- TEXT:
这两个结果刻画了那些是 ``X`` 上拓扑空间结构的邻域函数的
``X → Filter X`` 函数。仍然有一个函数 ``TopologicalSpace.mkOfNhds : (X → Filter X) → TopologicalSpace X``，
但只有当它满足上述两个约束时，它才会将它的输入作为邻域函数返回。
更准确地说，我们有一个引理 ``TopologicalSpace.nhds_mkOfNhds``，它以不同的方式陈述了这一点，而我们
的下一个练习从我们上面的陈述方式推导出这个不同的方式。
BOTH: -/
#check TopologicalSpace.mkOfNhds

#check TopologicalSpace.nhds_mkOfNhds

-- QUOTE:
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro a s s_in
  refine ⟨{ y | s ∈ n y }, H a (fun x ↦ x ∈ s) s_in, ?_, by tauto⟩
  rintro y (hy : s ∈ n y)
  exact H₀ y hy

-- BOTH:
end

-- QUOTE.
/- TEXT:
注意，``TopologicalSpace.mkOfNhds`` 并不那么常用，但仍然需要知道
在何种精确意义下邻域滤子就是拓扑空间结构的全部。

为了在 Mathlib 中高效地使用拓扑空间，接下来需要知道的是，我们大量使用了
``TopologicalSpace : Type u → Type u`` 的形式性质。从纯数学的观点来看，
这些形式性质是解释拓扑空间如何解决度量空间所具有的问题的一种非常清晰的方式。
从这个观点来看，拓扑空间解决的问题是，度量空间享有非常
少的函子性，并且通常具有非常差的范畴性质。这另加在
已经讨论过的度量空间包含许多拓扑上不相关的几何信息这一事实之上。

让我们首先关注函子性。度量空间结构可以被诱导到一个子集上，或者
等价地，可以通过一个单射拉回。但这基本上就是全部了。
它们不能通过一般的映射拉回，也不能被前推，即使是通过满射。

特别地，在度量空间的商空间或度量空间的不可数积上都没有合理的距离可放。
例如，考虑类型 ``ℝ → ℝ``，视为由 ``ℝ`` 索引的 ``ℝ`` 的拷贝的
积。我们希望说函数列的逐点收敛是一个值得尊敬的收敛概念。
但在 ``ℝ → ℝ`` 上没有距离能够给出这个收敛概念。
相关地，没有距离能够确保映射 ``f : X → (ℝ → ℝ)`` 是连续的当且仅当
``fun x ↦ f x t`` 对每个 ``t : ℝ`` 都连续。

我们现在回顾用于解决所有这些问题的数据。首先，我们可以使用任何映射 ``f : X → Y``
来将拓扑从一边前推或拉回。这两种运算构成一个 Galois 连接。

BOTH: -/
-- QUOTE:
variable {X Y : Type*}

example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced
-- QUOTE.

/- TEXT:
这些运算与函数的复合兼容。
像往常一样，前推是协变的，拉回是反变的，参见 ``coinduced_compose`` 和 ``induced_compose``。
在纸面上，我们将使用记号 :math:`f_*T` 表示 ``TopologicalSpace.coinduced f T`` 以及
:math:`f^*T` 表示 ``TopologicalSpace.induced f T``。
BOTH: -/
#check coinduced_compose

#check induced_compose

/- TEXT:

下一个重要部分是对于任意给定的结构，``TopologicalSpace X`` 上的完备格结构。
如果你认为拓扑主要是开集的数据，那么你期望
``TopologicalSpace X`` 上的序关系来自 ``Set (Set X)``，即你期望 ``t ≤ t'``
如果一个集合 ``u`` 对 ``t'`` 是开集，只要它对 ``t`` 是开集。然而，我们已经知道 Mathlib 侧重于
邻域而非开集，因此对于任何 ``x : X``，我们希望从拓扑空间到邻域的映射
``fun T : TopologicalSpace X ↦ @nhds X T x`` 是保序的。
而我们知道 ``Filter X`` 上的序关系被设计为确保有一个保序的
``principal : Set X → Filter X``，允许将滤子视为广义集合。
因此我们在 ``TopologicalSpace X`` 上使用的序关系与来自 ``Set (Set X)`` 的序关系是相反的。

BOTH: -/
-- QUOTE:
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl
-- QUOTE.

/- TEXT:

现在我们可以通过组合前推（或拉回）运算与序关系来恢复连续性。

BOTH: -/
-- QUOTE:
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le
-- QUOTE.

/- TEXT:
有了这个定义以及前推与复合的兼容性，我们
免费得到了泛性质：对于任何拓扑空间 :math:`Z`，
函数 :math:`g : Y → Z` 对拓扑 :math:`f_*T_X` 是连续的当且仅当
:math:`g ∘ f` 是连续的。

.. math::
  g \text{ continuous } &⇔ g_*(f_*T_X) ≤ T_Z \\
  &⇔ (g ∘ f)_* T_X ≤ T_Z \\
  &⇔ g ∘ f \text{ continuous}


BOTH: -/
-- QUOTE:
example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
      (g : Y → Z) :
    @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
      @Continuous X Z T_X T_Z (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]
-- QUOTE.

/- TEXT:
因此我们已经得到了商拓扑（使用投影映射作为 ``f``）。这还没有用到
对于所有 ``X``，``TopologicalSpace X`` 是一个完备格。现在让我们看看所有这些结构如何
通过抽象废话证明积拓扑的存在性。
我们在上面考虑了 ``ℝ → ℝ`` 的情况，但现在让我们考虑一般情况 ``Π i, X i``，对于
某个 ``ι : Type*`` 和 ``X : ι → Type*``。我们希望，对于任何拓扑空间 ``Z`` 和任何函数
``f : Z → Π i, X i``，``f`` 是连续的当且仅当 ``(fun x ↦ x i) ∘ f`` 对所有 ``i`` 都连续。
让我们使用记号 :math:`p_i` 表示投影
``(fun (x : Π i, X i) ↦ x i)``，在"纸面上"探索这个约束：

.. math::
  (∀ i, p_i ∘ f \text{ continuous}) &⇔ ∀ i, (p_i ∘ f)_* T_Z ≤ T_{X_i} \\
  &⇔ ∀ i, (p_i)_* f_* T_Z ≤ T_{X_i}\\
  &⇔ ∀ i, f_* T_Z ≤ (p_i)^*T_{X_i}\\
  &⇔  f_* T_Z ≤ \inf \left[(p_i)^*T_{X_i}\right]

因此我们看到了我们想要的 ``Π i, X i`` 上的拓扑是什么：
BOTH: -/
-- QUOTE:
example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
  rfl
-- QUOTE.

/- TEXT:

这结束了我们对 Mathlib 如何看待拓扑空间通过成为一个更具函子性的理论
且在任意固定类型上具有完备格结构来修复度量空间理论的缺陷的巡礼。

分离性与可数性
^^^^^^^^^^^^^^^^^^^^^^^^^^^

我们看到拓扑空间的范畴具有非常好的性质。为此付出的代价是
存在相当病态的拓扑空间。
你可以对拓扑空间施加一些假设，以确保其行为
更接近度量空间的行为。最重要的是 ``T2Space``，也称为 "Hausdorff"，
它将确保极限是唯一的。
更强的分离性质是 ``T3Space``，它额外确保了 `RegularSpace` 性质：
每个点都有一个闭邻域基。

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a
-- QUOTE.

/- TEXT:
注意，在每个拓扑空间中，根据定义，每个点都有一个开邻域基。

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x
-- QUOTE.

/- TEXT:
我们现在的主要目标是证明允许通过连续性进行扩张的基本定理。
来自 Bourbaki 的《一般拓扑学》，I.8.5，定理 1（只取非平凡蕴含方向）：

设 :math:`X` 是一个拓扑空间，:math:`A` 是 :math:`X` 的稠密子集，:math:`f : A → Y`
是 :math:`A` 到 :math:`T_3` 空间 :math:`Y` 的连续映射。如果对于 :math:`X` 中的每个
:math:`x`，当 :math:`y` 趋近于 :math:`x` 同时保持在 :math:`A` 中时，
:math:`f(y)` 趋近于 :math:`Y` 中的一个极限，那么存在 :math:`f` 到
:math:`X` 的连续扩张 :math:`φ`。

实际上，Mathlib 包含了上述引理的一个更一般的版本，``IsDenseInducing.continuousAt_extend``，
但这里我们将坚持 Bourbaki 的版本。

回忆一下，给定 ``A : Set X``，``↥A`` 是与 ``A`` 关联的子类型，Lean 将在
需要时自动插入那个有趣的上箭头。而（包含）强制映射是 ``(↑) : A → X``。
假设"趋近于 :math:`x` 同时保持在 :math:`A` 中"对应于拉回滤子
``comap (↑) (𝓝 x)``。

让我们首先证明一个辅助引理，提取出来以简化上下文
（特别地，这里我们不需要 Y 是拓扑空间）。

BOTH: -/
-- QUOTE:
theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
/- EXAMPLES:
  sorry

SOLUTIONS: -/
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
-- QUOTE.

/- TEXT:
现在让我们转向连续性扩张定理的主要证明。

当 Lean 需要 ``↥A`` 上的拓扑时，它将自动使用诱导拓扑。
唯一相关的引理是
``nhds_induced (↑) : ∀ a : ↥A, 𝓝 a = comap (↑) (𝓝 ↑a)``
（这实际上是关于诱导拓扑的一般引理）。

证明大纲是：

主要假设和选择公理给出一个函数 ``φ`` 使得
``∀ x, Tendsto f (comap (↑) (𝓝 x)) (𝓝 (φ x))``
（因为 ``Y`` 是 Hausdorff 的，``φ`` 是完全确定的，但直到我们尝试
证明 ``φ`` 确实是 ``f`` 的扩张时才会需要这一点）。

让我们首先证明 ``φ`` 是连续的。固定任意 ``x : X``。
因为 ``Y`` 是正则的，只需检查对于 ``φ x`` 的每个*闭*邻域
``V'``，都有 ``φ ⁻¹' V' ∈ 𝓝 x``。
极限假设给出（通过上面的辅助引理）
某个 ``V ∈ 𝓝 x`` 使得 ``IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V'``。
因为 ``V ∈ 𝓝 x``，只需证明 ``V ⊆ φ ⁻¹' V'``，即 ``∀ y ∈ V, φ y ∈ V'``。
固定 ``y`` 在 ``V`` 中。因为 ``V`` 是*开*的，它是 ``y`` 的邻域。
特别地 ``(↑) ⁻¹' V ∈ comap (↑) (𝓝 y)``，因此更有 ``f ⁻¹' V' ∈ comap (↑) (𝓝 y)``。
此外 ``comap (↑) (𝓝 y) ≠ ⊥``，因为 ``A`` 是稠密的。
因为我们知道 ``Tendsto f (comap (↑) (𝓝 y)) (𝓝 (φ y))``，这蕴含
``φ y ∈ closure V'``，并且由于 ``V'`` 是闭的，我们证明了 ``φ y ∈ V'``。

还需要证明 ``φ`` 扩张了 ``f``。这是 ``f`` 的连续性以及
``Y`` 是 Hausdorff 的这一事实进入讨论的地方。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
/- EXAMPLES:
  sorry

#check HasBasis.tendsto_right_iff

SOLUTIONS: -/
  choose φ hφ using hf
  use φ
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 x by
      simpa [ContinuousAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
    intro V' V'_in V'_closed
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V' := aux (hφ x) V'_in
    suffices : ∀ y ∈ V, φ y ∈ V'
    exact mem_of_superset V_in this
    intro y y_in
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in
    haveI : (comap ((↑) : A → X) (𝓝 y)).NeBot := by simpa [mem_closure_iff_comap_neBot] using hA y
    apply V'_closed.mem_of_tendsto (hφ y)
    exact mem_of_superset (preimage_mem_comap hVx) hV
  · intro a
    have lim : Tendsto f (𝓝 a) (𝓝 (φ a)) := by simpa [nhds_induced] using hφ a
    exact tendsto_nhds_unique lim f_cont.continuousAt
-- QUOTE.

/- TEXT:
除了分离性质之外，你可以对拓扑空间施加的主要假设类型
是使其更接近度量空间的可数性假设。主要的是第一可数性，
要求每个点都有一个可数的邻域基。特别地，这确保了集合的闭包
可以使用序列来理解。

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [FirstCountableTopology X]
      {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
  mem_closure_iff_seq_limit
-- QUOTE.

/- TEXT:
紧性
^^^^^^^^^^^

现在让我们讨论拓扑空间中紧性是如何定义的。像往常一样，有几种方式
来思考它，而 Mathlib 选择了滤子版本。

我们首先需要定义滤子的聚点。给定拓扑空间 ``X`` 上的滤子 ``F``，
点 ``x : X`` 是 ``F`` 的聚点，如果 ``F``（视为广义集合）与
接近 ``x`` 的点的广义集合有非空的交。

然后我们可以说集合 ``s`` 是紧的，如果包含在 ``s`` 中的每个非空广义集合 ``F``，
即满足 ``F ≤ 𝓟 s``，在 ``s`` 中都有一个聚点。

BOTH: -/
-- QUOTE:
variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl
-- QUOTE.

/- TEXT:
例如，如果 ``F`` 是 ``map u atTop``，即 ``atTop``（非常大的自然数的广义集合）
在 ``u : ℕ → X`` 下的像，那么假设 ``F ≤ 𝓟 s`` 意味着 ``u n`` 对足够大的 ``n``
属于 ``s``。说 ``x`` 是 ``map u atTop`` 的聚点意味着非常大的数的像
与接近 ``x`` 的点的集合相交。在 ``𝓝 x`` 具有可数基的情况下，我们可以
将这解释为 ``u`` 有一个收敛到 ``x`` 的子列，从而我们回到了度量空间中
紧性的样貌。
BOTH: -/
-- QUOTE:
example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu
-- QUOTE.

/- TEXT:
聚点与连续函数有良好的交互。

BOTH: -/
-- QUOTE:
variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf
-- QUOTE.

/- TEXT:
作为练习，我们将证明紧集在连续映射下的像也是
紧的。除了我们已经看到的内容之外，你还应该使用 ``Filter.push_pull`` 和
``NeBot.of_map``。
BOTH: -/
-- QUOTE:
-- EXAMPLES:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by sorry
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by sorry
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  sorry
-- QUOTE.

-- SOLUTIONS:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by rw [Filter.push_pull, map_principal]
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by
    apply NeBot.of_map
    rwa [map_eq, inf_of_le_right F_le]
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  rcases hs Hle with ⟨x, x_in, hx⟩
  refine ⟨f x, mem_image_of_mem f x_in, ?_⟩
  apply hx.map hf.continuousAt
  rw [Tendsto, map_eq]
  exact inf_le_right

/- TEXT:
紧性也可以用开覆盖来表达：``s`` 是紧的，如果覆盖
``s`` 的任意开集族都有一个有限覆盖子族。

BOTH: -/
-- QUOTE:
example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU
-- QUOTE.
