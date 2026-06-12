import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/- TEXT:
.. _counting_arguments:

计数论证
------------------

计数的艺术是组合数学的核心部分。
Mathlib 包含几个用于计算有限集元素数量的基本恒等式：
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]
-- QUOTE.

/- TEXT:
打开 ``Finset`` 命名空间允许我们使用记号 ``#s`` 表示 ``s.card``，以及
使用简写名称 `card_union` 等。

Mathlib 也可以计算有限类型的元素数量：
EXAMPLES: -/
section
-- QUOTE:
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp
-- QUOTE.

end

/- TEXT:
当 ``Fintype`` 命名空间未打开时，我们必须使用 ``Fintype.card`` 而不是 `card`。

以下是一个计算有限集基数（即 `range n` 与一个平移超过 `n` 的 `range n` 的副本
的并集）的例子。
该计算需要证明并集中的两个集合是不相交的；
证明的第一行产生了附加条件
``Disjoint (range n) (image (fun i ↦ m + i) (range n))``，该条件在证明末尾
得到确立。
``Disjoint`` 谓词对我们来说太一般化了，不能直接使用，但定理
``disjoint_iff_ne`` 将其转化为我们可以使用的形式。
EXAMPLES: -/
-- QUOTE:
#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective, card_range]; omega
  . apply add_right_injective
  . simp [disjoint_iff_ne]; omega
-- QUOTE.

/- TEXT:
在本节中，``omega`` 将是我们的主力工具，用于处理算术计算和不等式。

这里有一个更有趣的例子。考虑由满足 :math:`i < j` 的
序对 :math:`(i, j)` 组成的
:math:`\{0, \ldots, n\} \times \{0, \ldots, n\}` 的子集。
如果你将这些看作坐标平面上的格点，它们构成以 :math:`(0, 0)` 和
:math:`(n, n)` 为顶点的正方形的上三角，
不包含对角线。整个正方形的基数是 :math:`(n + 1)^2`，去掉对角线的
大小并将结果减半，告诉我们该三角形的基数是
:math:`n (n + 1) / 2`。

或者，我们注意到三角形的各行大小分别为 :math:`0, 1, \ldots, n`，因此
基数是前 :math:`n` 个正整数的和。下面证明的第一个 ``have``
将三角形描述为各行的并集，其中第 :math:`j` 行由
与 :math:`j` 配对的数据 :math:`0, 1, ..., j - 1` 组成。
在下面的证明中，记号 ``(., j)`` 缩写函数
``fun i ↦ (i, j)``。证明的其余部分只是有限集基数的计算。
BOTH: -/
-- QUOTE:
def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (., j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    . rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    . rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- 先处理不相交性
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- 继续计算
  transitivity (∑ i ∈ range (n + 1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl
-- QUOTE.

/- TEXT:
以下证明的变体使用有限类型而不是有限集来进行计算。
类型 ``α ≃ β`` 是 ``α`` 和 ``β`` 之间等价关系的类型，由一个前向映射、
一个后向映射以及这两个映射互逆的证明组成。
证明中的第一个 ``have`` 展示了 ``triangle n`` 等价于
``Fin (n + 1)`` 中 ``i`` 遍历时的 ``Fin i`` 的不交并。有趣的是，前向
函数和反向函数是用策略构造的，而不是显式写出的。
由于它们所做的仅仅是在数据和信息之间移动，``rfl`` 就确立了它们
互逆。

此后，``rw [←Fintype.card_coe]`` 将 ``#(triangle n)`` 重写为子类型
``{ x // x ∈ triangle n }`` 的基数，证明的其余部分是一个计算。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        have : (i ≤ n ∧ j ≤ n) ∧ i < j := by simpa [triangle] using hp
        exact ⟨⟨j, by linarith⟩, ⟨i, by linarith⟩⟩
      invFun := by
        rintro ⟨i, j⟩
        use ⟨j, i⟩
        suffices j ≤ n ∧ i ≤ n by simpa [triangle]
        constructor <;> linarith [i.2, j.2]
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all
-- QUOTE.

/- TEXT:
这是另一种方法。下面证明的第一行将问题归结为证明
``2 * #(triangle n) = (n + 1) * n``。我们可以通过证明三角形的两个副本
恰好填满矩形 ``range n ×ˢ range (n + 1)`` 来做到这一点。
作为练习，看看你能否填写计算的步骤。
在解答中，我们在倒数第二步大量依赖了 ``omega``，
但不幸的是我们不得不手动完成相当多的工作。
BOTH: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          ring
BOTH: -/
    _ = #(triangle n) + #(triangle n |>.image turn) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [Finset.card_image_of_injOn]
          rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn]
          simp_all [triangle]; omega
BOTH: -/
    _ = #(range n ×ˢ range (n + 1)) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [←Finset.card_union_of_disjoint]; swap
          . rw [Finset.disjoint_iff_ne]
            rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn] at *
            simp_all [triangle]; omega
          congr; ext p; rcases p with ⟨p1, p2⟩
          simp [triangle, turn]
          constructor
          . rintro (h | h) <;> omega
          rcases Nat.lt_or_ge p1 p2 with h | h
          . omega
          . intro h'
            right
            use n - 1 - p1, n - p2
            omega
BOTH: -/
    _ = (n + 1) * n := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          simp [mul_comm]
BOTH: -/
-- QUOTE.

/- TEXT:
你可以说服自己，如果我们在 ``triangle`` 的定义中将 ``n`` 替换为
``n + 1``
并将 ``<`` 替换为 ``≤``，我们会得到相同的三角形，只是向下平移了。
下面的练习要求你使用这个事实来证明这两个三角形具有相同的大小。
BOTH: -/
-- QUOTE:
def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by sorry
/- SOLUTIONS:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let f (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have : triangle n = (triangle' n |>.image f) := by
    ext p; rcases p with ⟨p1, p2⟩
    simp [triangle, triangle', f]
    constructor
    . intro h
      use p1, p2 - 1
      omega
    . simp; omega
  rw [this, card_image_of_injOn]
  rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [f]
BOTH: -/
-- QUOTE.

/- TEXT:
让我们用 Bhavik Mehta 在 2023 年《Lean for the Curious Mathematician》上给出的
一个组合数学 `教程 <https://www.youtube.com/watch?v=_cJctOIXWE4&list=PLlF-CfQhukNn7xEbfL38eLgkveyk9_myQ&index=8&t=2737s&ab_channel=leanprovercommunity>`_
中的一个例子和练习来结束本节。
假设我们有一个二部图，其顶点集为 ``s`` 和 ``t``，使得对于 ``s`` 中的每个 ``a``，
至少有 3 条边从 ``a`` 出发，并且对于 ``t`` 中的每个 ``b``，至多
有 1 条边进入 ``b``。那么图中边的总数至少是 ``s`` 的基数的三倍，
且至多是 ``t`` 的基数，由此得出 ``s`` 的基数的三倍至多是 ``t`` 的基数。
以下定理实现了这个论证，其中我们使用关系 ``r`` 来表示
图的边。该证明是一个优雅的计算。
EXAMPLES: -/
section
-- QUOTE:
open Classical
variable (s t : Finset ℕ) (a b : ℕ)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc 3 * #(s)
      = ∑ a ∈ s, 3                               := by simp [mul_comm]
    _ ≤ ∑ a ∈ s, #({b ∈ t | r a b})              := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #({a ∈ s | r a b})              := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ ≤ #(t)                                     := by simp
-- QUOTE.

/- TEXT:
以下练习也取自 Mehta 的教程。假设 ``A`` 是 ``range (2 * n)`` 的
一个含有 ``n + 1`` 个元素的子集。
容易看出 ``A`` 必定包含两个
连续整数，因此包含两个互质的元素。
如果你观看教程，你会看到在证明以下事实时花费了大量精力，
而该事实现在可以由 ``omega`` 自动证明。
EXAMPLES: -/
-- QUOTE:
example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega
-- QUOTE.

/- TEXT:
Mehta 练习的解答使用鸽巢原理，其形式为
``exists_lt_card_fiber_of_mul_lt_card_of_maps_to``，来证明在 ``A`` 中存在两个不同的
元素 ``m`` 和 ``k`` 使得 ``m / 2 = k / 2``。
看看你能否完成该事实的论证，然后用它来完成证明。
BOTH: -/
-- QUOTE:
example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
-- EXAMPLES:
    · sorry
/- SOLUTIONS:
    · intro u hu
      specialize hA' hu
      simp only [mem_range] at *
      exact Nat.div_lt_of_lt_mul hA'
EXAMPLES: -/
    · sorry
/- SOLUTIONS:
    · simp [hA]
BOTH: -/
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
-- EXAMPLES:
  sorry
/- SOLUTIONS:
  rcases ht' with ⟨m, ⟨hm, hm'⟩, k, ⟨hk, hk'⟩, hmk⟩
  use m, hm, k, hk
  have : m = k + 1 ∨ k = m + 1 := by omega
  rcases this with h | h <;> simp [h]
BOTH: -/
-- QUOTE.
