import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

/- TEXT:
.. index:: Filter

.. _filters:

滤子
-------

类型 ``X`` 上的一个*滤子*是 ``X`` 的集合的一个收集，它满足三个
条件，我们将在下面详细说明。这个概念
支持两个相关的思想：

* *极限*，包括上面讨论的所有类型的极限：序列的有限和无穷极限，函数在一点或无穷远处的有限和无穷极限，等等。

* *最终发生的事*，包括对于足够大的 ``n : ℕ`` 成立的事，或对于足够接近点 ``x`` 的点成立的事，或对于足够接近的点对成立的事，或在测度论意义下几乎处处成立的事。对偶地，滤子也可以表达*经常发生的事*的概念：对任意大的 ``n``，在给定点的任何邻域中的点，等等。

对应于这些描述的滤子将在本节后面定义，但我们已经可以命名它们：

* ``(atTop : Filter ℕ)``，由 ``ℕ`` 中包含对于某个 ``N`` 的 ``{n | n ≥ N}`` 的集合组成
* ``𝓝 x``，由拓扑空间中 ``x`` 的邻域组成
* ``𝓤 X``，由一致空间的邻近集组成（一致空间推广了度量空间和拓扑群）
* ``μ.ae``，由关于测度 ``μ`` 的补集具有零测度的集合组成。

一般定义如下：一个滤子 ``F : Filter X`` 是
集合的收集 ``F.sets : Set (Set X)``，满足以下条件：

* ``F.univ_sets : univ ∈ F.sets``
* ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
* ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``。

第一个条件说 ``X`` 的所有元素的集合属于 ``F.sets``。
第二个条件说如果 ``U`` 属于 ``F.sets``，那么任何
包含 ``U`` 的集合也属于 ``F.sets``。
第三个条件说 ``F.sets`` 对有限交封闭。
在 Mathlib 中，滤子 ``F`` 被定义为打包 ``F.sets`` 及其
三个性质的结构体，但这些性质不携带额外数据，
而且模糊 ``F`` 和 ``F.sets`` 之间的区别是很方便的。我们
因此定义 ``U ∈ F`` 为 ``U ∈ F.sets``。
这就解释了为什么在那些提及 ``U ∈ F`` 的引理中，
``sets`` 这个词会出现在一些引理的名称中。

将滤子视为定义了一种"足够大"的集合的概念可能有所帮助。第一个
条件然后说 ``univ`` 是足够大的，第二个条件说包含一个足够
大的集合的集合也是足够大的，第三个条件说两个足够大的集合的交
也是足够大的。

将类型 ``X`` 上的滤子视为 ``Set X`` 的广义元素可能更有用。
例如，``atTop`` 是"非常大数的集合"，而 ``𝓝 x₀`` 是"非常接近 ``x₀`` 的点的集合"。
这种观点的一个体现是，我们可以将任何 ``s : Set X`` 关联到所谓的*主滤子*，
它由所有包含 ``s`` 的集合组成。
这个定义已经在 Mathlib 中，并有记号 ``𝓟``（局部化在 ``Filter`` 命名空间中）。
为了演示的目的，我们请你借此机会在这里完成这个定义。
EXAMPLES: -/
-- QUOTE:
def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry
-- QUOTE.

-- SOLUTIONS:
-- 在下一个例子中，我们可以在每个证明中使用 `tauto` 而不必知道这些引理
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }

/- TEXT:
对于我们的第二个例子，我们请你定义滤子 ``atTop : Filter ℕ``。
（我们可以使用任何具有预序的类型来代替 ``ℕ``。）
EXAMPLES: -/
-- QUOTE:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := sorry
    sets_of_superset := sorry
    inter_sets := sorry }
-- QUOTE.

-- SOLUTIONS:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use 42
      simp
    sets_of_superset := by
      rintro U V ⟨N, hN⟩ hUV
      use N
      tauto
    inter_sets := by
      rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
      use max N N'
      intro b hb
      rw [max_le_iff] at hb
      constructor <;> tauto }

/- TEXT:
我们也可以直接定义任何 ``x : ℝ`` 的邻域滤子 ``𝓝 x``。
在实数中，``x`` 的邻域是包含一个开区间
:math:`(x_0 - \varepsilon, x_0 + \varepsilon)` 的集合，
在 Mathlib 中定义为 ``Ioo (x₀ - ε) (x₀ + ε)``。
（这种邻域的概念只是 Mathlib 中更一般构造的一个特例。）

有了这些例子，我们已经可以定义函数 ``f : X → Y``
沿某个 ``F : Filter X`` 收敛到某个 ``G : Filter Y`` 的含义，
如下：
BOTH: -/
-- QUOTE:
def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- TEXT:
当 ``X`` 是 ``ℕ`` 且 ``Y`` 是 ``ℝ`` 时，``Tendsto₁ u atTop (𝓝 x)`` 等价于说序列 ``u : ℕ → ℝ``
收敛到实数 ``x``。当 ``X`` 和 ``Y`` 都是 ``ℝ`` 时，``Tendsto f (𝓝 x₀) (𝓝 y₀)``
等价于熟悉的概念 :math:`\lim_{x \to x₀} f(x) = y₀`。
引言中提到的所有其他类型的极限也等价于
在源和目标上适当选择滤子后的 ``Tendsto₁`` 的实例。

上面的概念 ``Tendsto₁`` 按定义等价于 Mathlib 中定义的概念 ``Tendsto``，
但后者是更抽象地定义的。
``Tendsto₁`` 的定义的问题在于它暴露了一个量词和 ``G`` 的元素，
并隐藏了我们将滤子视为广义集合所获得的直觉。我们可以
通过使用更多的代数和集合论机制，隐藏量词 ``∀ V`` 并使直觉更加突出。
第一个要素是与任何映射 ``f : X → Y`` 相关联的*前推*运算 :math:`f_*`，
在 Mathlib 中记为 ``Filter.map f``。给定 ``X`` 上的滤子 ``F``，``Filter.map f F : Filter Y`` 的定义使得
``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F`` 按定义成立。
在示例文件中，我们打开了 ``Filter`` 命名空间，因此
``Filter.map`` 可以写成 ``map``。这意味着我们可以使用 ``Filter Y``
上的序关系来重写 ``Tendsto`` 的定义，该序关系是成员集合的逆包含。
换句话说，给定 ``G H : Filter Y``，我们有 ``G ≤ H ↔ ∀ V : Set Y, V ∈ H → V ∈ G``。
EXAMPLES: -/
-- QUOTE:
def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl
-- QUOTE.

/- TEXT:
看起来滤子上的序关系是反向的。但回忆一下，我们可以将 ``X`` 上的滤子视为
``Set X`` 的广义元素，通过包含映射 ``𝓟 : Set X → Filter X`` 将任意集合 ``s`` 映射到相应的主滤子。
这个包含是保序的，因此 ``Filter`` 上的序关系确实可以看作广义集合之间
的自然包含关系。在这个类比下，前推类似于直接像。
而且，确实，``map f (𝓟 s) = 𝓟 (f '' s)``。

现在我们可以直观地理解为什么序列 ``u : ℕ → ℝ`` 收敛到
点 ``x₀`` 当且仅当我们有 ``map u atTop ≤ 𝓝 x₀``。
这个不等式意味着 ``u`` 下的"非常大的自然数的集合"的直接像
"包含"在"非常接近 ``x₀`` 的点的集合"中。

正如承诺的，``Tendsto₂`` 的定义不展示任何量词或集合。
它也利用了前推运算的代数性质。
首先，每个 ``Filter.map f`` 是单调的。其次，``Filter.map`` 与
复合兼容。
EXAMPLES: -/
-- QUOTE:
#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)
-- QUOTE.

/- TEXT:
这两个性质一起允许我们证明极限可以复合，一举得到引言中描述的
复合引理的所有 512 种变体，以及更多的变体。
你可以练习证明以下陈述，使用 ``Tendsto₁`` 的
涉及全称量词的定义或代数定义，
以及上面的两个引理。
EXAMPLES: -/
-- QUOTE:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg


example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  intro V hV
  rw [preimage_comp]
  apply hf
  apply hg
  exact hV

/- TEXT:
前推构造使用映射将滤子从映射的源推向映射的目标。
还有一个*拉回*运算 ``Filter.comap``，沿相反方向。
这推广了集合上的原像运算。对于任何映射 ``f``，
``Filter.map f`` 和 ``Filter.comap f`` 构成了所谓的 *Galois 连接*，
即它们满足

  ``Filter.map_le_iff_le_comap : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G``

对于每个 ``F`` 和 ``G``。
这个运算可以用来提供 ``Tendsto`` 的另一种表述，该表述与
Mathlib 中的表述可证明地等价（但非定义上等价）。

``comap`` 运算可用于将滤子限制到子类型。例如，假设我们有 ``f : ℝ → ℝ``，
``x₀ : ℝ`` 和 ``y₀ : ℝ``，并且我们想陈述当 ``x`` 在有理数范围内趋近于 ``x₀`` 时 ``f x`` 趋近于 ``y₀``。
我们可以使用强制映射
``(↑) : ℚ → ℝ`` 将滤子 ``𝓝 x₀`` 拉回到 ``ℚ``，然后陈述 ``Tendsto (f ∘ (↑) : ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)``。
EXAMPLES: -/
-- QUOTE:
variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- TEXT:
拉回运算也与复合兼容，但它是*反变的*，
即它反转参数的顺序。
EXAMPLES: -/
-- QUOTE:
section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end
-- QUOTE.

/- TEXT:
现在让我们将注意力转向平面 ``ℝ × ℝ``，尝试理解点
``(x₀, y₀)`` 的邻域与 ``𝓝 x₀`` 和 ``𝓝 y₀`` 的关系。有一个积运算
``Filter.prod : Filter X → Filter Y → Filter (X × Y)``，记为 ``×ˢ``，它回答了这个问题：
EXAMPLES: -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq
-- QUOTE.

/- TEXT:
积运算是通过拉回运算和 ``inf`` 运算定义的：

  ``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``。

这里 ``inf`` 运算指的是对于任何类型 ``X``，``Filter X`` 上的格结构，其中
``F ⊓ G`` 是比 ``F`` 和 ``G`` 都小的最大滤子。
因此 ``inf`` 运算推广了集合交集的概念。

Mathlib 中有很多证明使用上述所有结构（``map``、``comap``、``inf``、``sup`` 和 ``prod``）
来给出关于收敛的代数证明，而从不引用滤子的成员。
你可以尝试在以下引理的证明中实践这一点，如果需要，
展开 ``Tendsto`` 和 ``Filter.prod`` 的定义。
EXAMPLES: -/
-- QUOTE:
#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  calc
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔ map f atTop ≤ 𝓝 (x₀, y₀) := Iff.rfl
    _ ↔ map f atTop ≤ 𝓝 x₀ ×ˢ 𝓝 y₀ := by rw [nhds_prod_eq]
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ⊓ comap Prod.snd (𝓝 y₀) := Iff.rfl
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ∧ map f atTop ≤ comap Prod.snd (𝓝 y₀) := le_inf_iff
    _ ↔ map Prod.fst (map f atTop) ≤ 𝓝 x₀ ∧ map Prod.snd (map f atTop) ≤ 𝓝 y₀ := by
      rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
    _ ↔ map (Prod.fst ∘ f) atTop ≤ 𝓝 x₀ ∧ map (Prod.snd ∘ f) atTop ≤ 𝓝 y₀ := by
      rw [map_map, map_map]


-- 另一种解法
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  rw [nhds_prod_eq]
  unfold Tendsto SProd.sprod Filter.instSProd
  rw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]

/- TEXT:
有序类型 ``Filter X`` 实际上是一个*完备*格，
即存在底元素，存在顶元素，且
``X`` 上的每个滤子集合都有一个 ``Inf`` 和一个 ``Sup``。

注意，给定滤子定义中的第二个性质
（如果 ``U`` 属于 ``F``，则任何比 ``U`` 大的集合也属于 ``F``），
第一个性质
（``X`` 的所有元素的集合属于 ``F``）等价于
``F`` 不是空集合的收集这一性质。
这不应与空集是否是 ``F`` 的*元素*这一更微妙的问题混淆。滤子的
定义不禁止 ``∅ ∈ F``，
但如果空集属于 ``F``，那么
每个集合都属于 ``F``，即 ``∀ U : Set X, U ∈ F``。
在这种情况下，``F`` 是一个相当平凡的滤子，它恰好是
完备格 ``Filter X`` 的底元素。
这与 Bourbaki 中滤子的定义形成对比，
后者不允许滤子包含空集。

因为我们在定义中包含了平凡滤子，有时需要在某些引理中显式假设
非平凡性。
然而，作为回报，该理论具有更好的整体性质。
我们已经看到，包含平凡滤子给了我们一个
底元素。它还允许我们定义 ``principal : Set X → Filter X``，
它将 ``∅`` 映射到 ``⊥``，而无需添加排除空集的前提条件。
而且它也允许我们在没有前提条件的情况下定义拉回运算。
事实上，尽管 ``F ≠ ⊥``，也可能发生 ``comap f F = ⊥``。例如，
给定 ``x₀ : ℝ`` 和 ``s : Set ℝ``，``𝓝 x₀`` 在从对应于 ``s`` 的子类型的强制映射下的拉回
是非平凡的当且仅当 ``x₀`` 属于
``s`` 的闭包。

为了管理那些确实需要假设某个滤子是非平凡的引理，Mathlib 有一个
类型类 ``Filter.NeBot``，库中有引理假设
``(F : Filter X) [F.NeBot]``。实例数据库知道，例如，``(atTop : Filter ℕ).NeBot``，
并且知道前推一个非平凡滤子会给出一个非平凡滤子。
因此，对于任何序列 ``u``，假设 ``[F.NeBot]`` 的引理将自动应用于 ``map u atTop``。

我们对滤子的代数性质及其与极限关系的巡礼基本上完成了，
但我们还没有证明我们重新捕获了通常的极限概念这一主张。
表面上，``Tendsto u atTop (𝓝 x₀)``
似乎比 :numref:`sequences_and_convergence` 中定义的收敛概念更强，因为我们要
求 *每个* ``x₀`` 的邻域都有一个属于 ``atTop`` 的原像，而通常的定义只对
标准邻域 ``Ioo (x₀ - ε) (x₀ + ε)`` 要求这一点。
关键在于，根据定义，每个邻域都包含这样一个标准邻域。
这个观察导致了*滤子基*的概念。

给定 ``F : Filter X``，
一族集合 ``s : ι → Set X`` 是 ``F`` 的一个基，如果对于每个集合 ``U``，
我们有 ``U ∈ F`` 当且仅当它包含某个 ``s i``。换句话说，形式地说，
``s`` 是一个基如果它满足
``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U``。考虑索引类型中
只选择某些值 ``i`` 的谓词甚至更加灵活。
在 ``𝓝 x₀`` 的情况下，我们希望 ``ι`` 是 ``ℝ``，我们记 ``i`` 为 ``ε``，且谓词应该选择正的 ``ε`` 值。
因此，集合 ``Ioo  (x₀ - ε) (x₀ + ε)`` 构成实数上邻域拓扑
的基这一事实陈述如下：
EXAMPLES: -/
-- QUOTE:
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀
-- QUOTE.

/- TEXT:
滤子 ``atTop`` 也有一个很好的基。引理
``Filter.HasBasis.tendsto_iff`` 允许我们在给定 ``F`` 和 ``G`` 的基的情况下
重新表述形如 ``Tendsto f F G`` 的陈述。
将这些拼在一起，基本上就给出了我们在 :numref:`sequences_and_convergence` 中使用的
收敛概念。
EXAMPLES: -/
-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
-- QUOTE.

/- TEXT:
现在我们来展示滤子如何促进对足够大数或足够接近给定点的点成立的性质的处理。
在 :numref:`sequences_and_convergence` 中，我们经常面临这样的情况：我们
知道某个性质 ``P n`` 对足够大的 ``n`` 成立，并且某个
其他性质 ``Q n`` 对足够大的 ``n`` 成立。
使用 ``cases`` 两次得到 ``N_P`` 和 ``N_Q`` 满足
``∀ n ≥ N_P, P n`` 和 ``∀ n ≥ N_Q, Q n``。使用 ``set N := max N_P N_Q``，我们可以
最终证明 ``∀ n ≥ N, P n ∧ Q n``。
反复这样做会变得乏味。

我们可以通过注意到陈述 "``P n`` 和 ``Q n`` 对足够大的 ``n`` 成立" 意味着
我们有 ``{n | P n} ∈ atTop`` 和 ``{n | Q n} ∈ atTop`` 来做得更好。
``atTop`` 是一个滤子这一事实意味着 ``atTop`` 的两个元素的交
仍然在 ``atTop`` 中，因此我们有 ``{n | P n ∧ Q n} ∈ atTop``。
写 ``{n | P n} ∈ atTop`` 很不舒服，
但我们可以使用更具提示性的记号 ``∀ᶠ n in atTop, P n``。
这里上标的 ``f`` 代表 "Filter"。
你可以将此记号理解为：对于"非常大数的集合"中的所有 ``n``，``P n`` 成立。``∀ᶠ``
记号代表 ``Filter.Eventually``，而引理 ``Filter.Eventually.and`` 使用滤子的交性质来实现我们刚才描述的内容：
EXAMPLES: -/
-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ
-- QUOTE.

/- TEXT:
这个记号如此方便和直观，以至于当 ``P`` 是一个等式或不等式陈述时，我们也有特化的版本。
例如，设 ``u`` 和 ``v`` 是两个实数序列，让我们证明如果
``u n`` 和 ``v n`` 对足够大的 ``n`` 重合，那么
``u`` 趋近于 ``x₀`` 当且仅当 ``v`` 趋近于 ``x₀``。
首先我们使用通用的 ``Eventually``，然后使用专门为
等式谓词特化的 ``EventuallyEq``。这两个陈述是
按定义等价的，因此相同的证明在两种情况下都有效。
EXAMPLES: -/
-- QUOTE:
example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h
-- QUOTE.

/- TEXT:
回顾一下关于滤子在 ``Eventually`` 方面的定义是很有益的。
给定 ``F : Filter X``，对于 ``X`` 上的任意谓词 ``P`` 和 ``Q``，

* 条件 ``univ ∈ F`` 确保 ``(∀ x, P x) → ∀ᶠ x in F, P x``，
* 条件 ``U ∈ F → U ⊆ V → V ∈ F`` 确保 ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``，以及
* 条件 ``U ∈ F → V ∈ F → U ∩ V ∈ F`` 确保 ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``。
EXAMPLES: -/
-- QUOTE:
#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and
-- QUOTE.

/- TEXT:
第二项，对应于 ``Eventually.mono``，支持使用滤子的好方法，
特别是当与 ``Eventually.and`` 结合时。
``filter_upwards`` 策略允许我们将它们组合起来。
对比：
EXAMPLES: -/
-- QUOTE:
example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩
-- QUOTE.

/- TEXT:
了解测度论的读者会注意到，由补集具有零测度的集合组成的滤子 ``μ.ae``
（也称为"几乎每个点组成的集合"）作为 ``Tendsto`` 的源或目标不太有用，但它可以方便地
与 ``Eventually`` 一起使用，说一个性质对几乎每个点成立。

``∀ᶠ x in F, P x`` 有一个对偶版本，偶尔有用：
``∃ᶠ x in F, P x`` 表示
``{x | ¬P x} ∉ F``。例如，``∃ᶠ n in atTop, P n`` 表示存在任意大的 ``n`` 使得 ``P n`` 成立。
``∃ᶠ`` 记号代表 ``Filter.Frequently``。

对于一个更复杂的例子，考虑以下关于序列
``u``、集合 ``M`` 和值 ``x`` 的陈述：

  如果 ``u`` 收敛到 ``x`` 并且对于足够大的 ``n``，``u n`` 属于 ``M``，
  那么 ``x`` 属于 ``M`` 的闭包。

这可以形式化如下：

  ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``。

这是拓扑库中定理 ``mem_closure_of_tendsto`` 的一个特例。
看看你能否使用引用的引理来证明它，
使用 ``ClusterPt x F`` 表示 ``(𝓝 x ⊓ F).NeBot`` 这一事实，以及
根据定义，假设 ``∀ᶠ n in atTop, u n ∈ M`` 意味着 ``M ∈ map u atTop``。
EXAMPLES: -/
-- QUOTE:
#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  mem_closure_iff_clusterPt.mpr (neBot_of_le <| le_inf hux <| le_principal_iff.mpr huM)
