import MIL.Common
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
.. index:: normed space

.. _normed_spaces:

赋范空间中的微分学
------------------

赋范空间
^^^^^^^^

微分学可以通过 *赋范向量空间* 的概念推广到 ``ℝ`` 之外，该概念同时刻画了方向与距离。
我们从 *赋范群* 的概念开始，它是一个装备了实值范数函数的加法交换群，
满足以下条件。
EXAMPLES: -/
section

-- QUOTE:
variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- QUOTE.

/- TEXT:
每个赋范空间都是度量空间，其距离函数为 :math:`d(x, y) = \| x - y \|`，因此它也是拓扑空间。
Lean 和 Mathlib 知道这一点。
EXAMPLES: -/
-- QUOTE:
example : MetricSpace E := by infer_instance

example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ :=
  hf.norm
-- QUOTE.

/- TEXT:
为了将范数的概念与线性代数的概念结合使用，
我们在 ``NormedAddGroup E`` 之上添加假设 ``NormedSpace ℝ E``。
这意味着 ``E`` 是 ``ℝ`` 上的向量空间，且标量乘法满足以下条件。
EXAMPLES: -/
-- QUOTE:
variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x
-- QUOTE.

/- TEXT:
完备的赋范空间称为 *Banach 空间*。
每个有限维向量空间都是完备的。
EXAMPLES: -/
-- QUOTE:
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance
-- QUOTE.

/- TEXT:
在前面的所有例子中，我们使用实数作为基域。
更一般地，我们可以在任意 *非平凡赋范域* 上的向量空间中理解微积分。
这些域装备了实值范数，该范数是乘性的，并且具有并非每个元素的范数都为零或一的性质
（等价地，存在一个元素其范数大于一）。
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜
-- QUOTE.

/- TEXT:
非平凡赋范域上的有限维向量空间是完备的，只要该域本身是完备的。
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E
-- QUOTE.

end

/- TEXT:
连续线性映射
^^^^^^^^^^^^

现在我们转向赋范空间范畴中的态射，即连续线性映射。
在 Mathlib 中，赋范空间 ``E`` 和 ``F`` 之间的 ``𝕜``-线性连续映射的类型
写作 ``E →L[𝕜] F``。
它们被实现为 *打包映射*，这意味着该类型的一个元素
是一个结构，它包含了映射函数本身以及线性性和连续性的性质。
Lean 会插入一个强制转换，使得连续线性映射可以被当作函数来使用。
EXAMPLES: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f :=
  f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x
-- QUOTE.

/- TEXT:
连续线性映射具有算子范数，其性质由以下特性刻画。
EXAMPLES: -/
-- QUOTE:
variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hMp hM
-- QUOTE.

end

/- TEXT:
此外，还有打包的连续线性 *同构* 的概念。
这类同构的类型是 ``E ≃L[𝕜] F``。

作为一个具有挑战性的练习，你可以证明 Banach-Steinhaus 定理，也称为一致有界原理。
该原理指出，从 Banach 空间到赋范空间的一族连续线性映射如果是逐点有界的，
则这些线性映射的范数是一致有界的。
主要成分是 Baire 定理 ``nonempty_interior_of_iUnion_of_closed``。
（你在拓扑章节中证明过该定理的一个版本。）
次要成分包括 ``continuous_linear_map.opNorm_le_of_shell``、
``interior_subset``、``interior_iInter_subset`` 和 ``isClosed_le``。
BOTH: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

-- EXAMPLES:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- 由满足对所有 i 有 ‖g i x‖ ≤ n 的 x : E 构成的子集序列
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- 每个这样的集合都是闭集
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- 它们的并是整个空间；这里我们用到了 `h`
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- 应用 Baire 范畴定理，推出对某个 `m : ℕ`，
       `e m` 包含某个 `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- 证明球中所有元素在应用任意 `g i` 后范数都不超过 `m`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- 由满足对所有 i 有 ‖g i x‖ ≤ n 的 x : E 构成的子集序列
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- 每个这样的集合都是闭集
  have hc : ∀ n : ℕ, IsClosed (e n) := fun i ↦
    isClosed_iInter fun i ↦ isClosed_le (g i).cont.norm continuous_const
  -- 它们的并是整个空间；这里我们用到了 `h`
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    rcases h x with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨e m, mem_range_self m, mem_iInter.mpr fun i ↦ le_trans (hC i) hm⟩
  /- 应用 Baire 范畴定理，推出对某个 `m : ℕ`，
       `e m` 包含某个 `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := NormedField.exists_one_lt_norm 𝕜
  -- 证明球中所有元素在应用任意 `g i` 后范数都不超过 `m`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    intro z hz i
    replace hz := mem_iInter.mp (interior_iInter_subset _ (hε hz)) i
    apply interior_subset hz
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk)
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) εk_pos.le
  intro y le_y y_lt
  calc
    ‖g i y‖ = ‖g i (y + x) - g i x‖ := by rw [(g i).map_add, add_sub_cancel_right]
    _ ≤ ‖g i (y + x)‖ + ‖g i x‖ := (norm_sub_le _ _)
    _ ≤ m + m :=
      (add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
        (real_norm_le x (mem_ball_self ε_pos) i))
    _ = (m + m : ℕ) := by norm_cast
    _ ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖)) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos ε_pos (zero_lt_one.trans hk)).2 le_y))
    _ = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ := (mul_comm_div _ _ _).symm


-- BOTH:
end

/- TEXT:
渐近比较
^^^^^^^^

定义可微性还需要渐近比较。
Mathlib 有一个广泛的库，涵盖了大 O 和小 o 关系，其定义如下所示。
打开 ``asymptotics`` 语言环境后，我们可以使用相应的记号。
这里我们仅用小 o 来定义可微性。
EXAMPLES: -/
-- QUOTE:
open Asymptotics

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl
-- QUOTE.

/- TEXT:
可微性
^^^^^^

现在我们准备讨论赋范空间之间的可微函数。
类似于一维初等情况，
Mathlib 定义了一个谓词 ``HasFDerivAt`` 和一个函数 ``fderiv``。
这里的字母 "f" 代表 *Fréchet*。
EXAMPLES: -/
section

-- QUOTE:
open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
  hasFDerivAtFilter_iff_isLittleO ..

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv
-- QUOTE.

/- TEXT:
我们还有迭代导数，其取值在多重线性映射类型 ``E [×n]→L[𝕜] F`` 中，
并且我们还有连续可微函数。
类型 ``ℕ∞`` 是 ``ℕ`` 附加一个比每个自然数都大的额外元素 ``∞``。
因此，:math:`\mathcal{C}^\infty` 函数是满足 ``ContDiff 𝕜 ⊤ f`` 的函数 ``f``。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f

example (n : ℕ∞) {f : E → F} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m f x :=
  contDiff_iff_continuous_differentiable
-- QUOTE.

/- TEXT:
``ContDiff`` 中的可微性参数也可以取值 ``ω : WithTop ℕ∞`` 来表示解析函数。

还有一种更严格的可微性概念，称为
``HasStrictFDerivAt``，它用于陈述
反函数定理和隐函数定理，这两者都在 Mathlib 中。
在 ``ℝ`` 或 ``ℂ`` 上，连续可微函数是严格可微的。
EXAMPLES: -/
-- QUOTE:
example {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt (zero_lt_one.trans_le hn).ne'
-- QUOTE.

/- TEXT:
局部反函数定理的陈述使用了一个运算，该运算从一个函数出发，
在假设该函数在点 ``a`` 处严格可微且其导数是同构的条件下，
产生一个反函数。

下面的第一个例子得到了这个局部反函数。
下一个例子说明它确实是一个左右局部反函数，并且它是严格可微的。
EXAMPLES: -/
-- QUOTE:
section LocalInverse
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  HasStrictFDerivAt.localInverse f f' a hf

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse

example {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFDerivAt.to_localInverse hf

end LocalInverse
-- QUOTE.

/- TEXT:
以上只是对 Mathlib 中微分学的一次快速巡览。
该库包含许多我们尚未讨论的变体。
例如，你可能想在一维环境中使用单侧导数。相关的方法可以在 Mathlib 中以更一般的上下文找到；
参见 ``HasFDerivWithinAt`` 或更一般的 ``HasFDerivAtFilter``。
EXAMPLES: -/
#check HasFDerivWithinAt

#check HasFDerivAtFilter

end
