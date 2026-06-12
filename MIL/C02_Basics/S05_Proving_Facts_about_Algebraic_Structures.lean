-- BOTH:
import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

/- TEXT:
.. _proving_facts_about_algebraic_structures:

证明关于代数结构的事实
----------------------------------------

.. index:: order relation, partial order

在 :numref:`proving_identities_in_algebraic_structures` 中，
我们看到许多控制实数的常见恒等式在更一般的代数结构类中也成立，
例如交换环。
我们可以使用我们想要的任何公理来描述代数结构，
不仅仅是等式。
例如，一个 *偏序* 由一个集合和一个
满足自反性、传递性和反对称性的二元关系组成，
就像实数上的 ``≤``。
Lean 了解偏序：
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- EXAMPLES:
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- QUOTE.

/- TEXT:
这里我们采用 Mathlib 的约定，使用
像 ``α``、``β`` 和 ``γ`` 这样的字母
（输入为 ``\a``、``\b`` 和 ``\g``）
来表示任意类型。
库经常使用像 ``R`` 和 ``G`` 这样的字母
分别表示环和群等代数结构的载体，
但一般来说，希腊字母用于表示类型，
特别是当与它们相关的结构很少或没有时。

与任何偏序 ``≤`` 相关联，
还有一个 *严格偏序*，``<``，
它在某种程度上像实数上的 ``<`` 一样运作。
在这个序中，说 ``x`` 小于 ``y``
等价于说它小于等于 ``y``
且不等于 ``y``。
TEXT. -/
-- QUOTE:
#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
-- QUOTE.

end

/- TEXT:
在这个例子中，符号 ``∧`` 表示"且"，
符号 ``¬`` 表示"非"，而
``x ≠ y`` 是 ``¬ (x = y)`` 的缩写。
在 :numref:`Chapter %s <logic>` 中，你将学习如何使用
这些逻辑连接词来 *证明* ``<``
具有所指出的性质。

.. index:: lattice

一个 *格* 是一个扩展偏序的结构，
带有运算 ``⊓`` 和 ``⊔``，它们
类似于实数上的 ``min`` 和 ``max``：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- EXAMPLES:
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- QUOTE.

/- TEXT:
对 ``⊓`` 和 ``⊔`` 的刻画使我们有理由将它们分别称为
*最大下界* 和 *最小上界*。
你可以在 VS Code 中使用 ``\glb`` 和 ``\lub`` 输入它们。
这些符号也经常被称为 *下确界* 和
*上确界*，
Mathlib 在定理名称中将它们称为 ``inf`` 和 ``sup``。
更复杂的是，
它们也经常被称为 *交* 和 *并*。
因此，如果你使用格，
你必须记住以下对照表：

* ``⊓`` 是 *最大下界*、*下确界* 或 *交*。

* ``⊔`` 是 *最小上界*、*上确界* 或 *并*。

格的一些实例包括：

* 任何全序上的 ``min`` 和 ``max``，例如带 ``≤`` 的整数或实数

* 某个域的子集集合上的 ``∩`` 和 ``∪``，以 ``⊆`` 为序

* 布尔真值上的 ``∧`` 和 ``∨``，以 ``x ≤ y`` 为序，如果 ``x`` 为假或 ``y`` 为真

* 自然数（或正整数）上的 ``gcd`` 和 ``lcm``，以整除序 ``∣`` 为序

* 向量空间的线性子空间的集合，
  其最大下界由交集给出，
  最小上界由两个空间的和给出，
  序为包含关系

* 集合（或在 Lean 中，类型）上的拓扑的集合，
  其中两个拓扑的最大下界由
  它们的并集生成的拓扑组成，
  最小上界是它们的交集，
  序为反向包含

你可以验证，与 ``min`` / ``max`` 和 ``gcd`` / ``lcm`` 一样，
你可以仅使用它们的刻画公理，
配合 ``le_refl`` 和 ``le_trans``，
证明下确界和上确界的交换性和结合性。

.. index:: trans, tactics ; trans

在看到目标 ``x ≤ z`` 时使用 ``apply le_trans`` 不是一个好主意。
实际上，Lean 无法猜测我们想要使用哪个中间元素 ``y``。
因此 ``apply le_trans`` 会产生三个目标，看起来像 ``x ≤ ?a``、``?a ≤ z``
和 ``α``，其中 ``?a``（可能带有更复杂的自动生成的名称）代表
神秘的 ``y``。
最后一个目标，类型为 ``α``，是提供 ``y`` 的值。
它排在最后是因为 Lean 希望从
第一个目标 ``x ≤ ?a`` 的证明中自动推断出它。
为了避免这种不优雅的局面，你可以使用 ``calc`` 策略
显式地提供 ``y``。
或者，你可以使用 ``trans`` 策略，
它以 ``y`` 为参数并产生预期的目标 ``x ≤ y`` 和
``y ≤ z``。
当然，你也可以通过直接提供完整的证明来避免这个问题，例如
``exact le_trans inf_le_left inf_le_right``，但这需要更多的
规划。
TEXT. -/
-- QUOTE:
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    trans y ⊔ z
    apply le_sup_right
    apply le_sup_right
  apply sup_le
  · trans x ⊔ y
    apply le_sup_left
    apply le_sup_left
  apply sup_le
  · trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
  apply le_sup_right

/- TEXT:
你可以在 Mathlib 中找到这些定理，分别名为 ``inf_comm``、``inf_assoc``、
``sup_comm`` 和 ``sup_assoc``。

另一个好的练习是仅使用这些公理证明 *吸收律*：
TEXT. -/
-- QUOTE:
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem absorb1αα : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2αα : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

-- BOTH:
end

/- TEXT:
这些可以在 Mathlib 中以名称 ``inf_sup_self`` 和 ``sup_inf_self`` 找到。

一个满足额外恒等式
``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` 和
``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)`` 的格
被称为 *分配格*。Lean 也了解这些：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
-- QUOTE.
end

/- TEXT:
左侧和右侧版本可以很容易地证明是等价的，
前提是 ``⊓`` 和 ``⊔`` 满足交换律。
证明并非每个格都是分配格
是一个好的练习——
通过提供一个具有有限个元素的非分配格的
显式描述。
在任意格中，证明
任一分配律蕴含另一个分配律也是一个好的练习：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- EXAMPLES:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

-- BOTH:
end

/- TEXT:
可以将公理化结构组合成更大的结构。
例如，一个 *严格有序环* 由一个环以及
载体上的一个偏序组成，
满足额外的公理，这些公理表明环运算
与序是兼容的：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

-- EXAMPLES:
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
-- QUOTE.

/- TEXT:
:numref:`Chapter %s <logic>` 将提供从 ``mul_pos``
和 ``<`` 的定义推导出以下内容的方法：
TEXT. -/
-- QUOTE:
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- QUOTE.

/- TEXT:
然后这是一个扩展练习，证明用于推理实数上的算术和排序的
许多常见事实对任何有序环都通用地成立。
这里是一些你可以尝试的例子，
仅使用环、偏序的性质以及
最后两个例子中列举的事实（注意这些环
并不假设是可交换的，因此 `ring` 策略不可用）：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_right h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_right h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

-- BOTH:
end

/- TEXT:
.. index:: metric space

最后，这里是最后一个例子。
一个 *度量空间* 由一个集合以及一个距离概念
``dist x y`` 组成，
将任意一对元素映射到一个实数。
距离函数假定满足以下公理：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

-- EXAMPLES:
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- QUOTE.

/- TEXT:
掌握了本节内容后，
你可以证明从这些公理可以推出距离总是非负的：
TEXT. -/
-- QUOTE:
example (x y : X) : 0 ≤ dist x y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- BOTH:
end

/- TEXT:
我们建议使用定理 ``nonneg_of_mul_nonneg_left``。
你可能已经猜到了，这个定理在 Mathlib 中被称为 ``dist_nonneg``。
TEXT. -/
