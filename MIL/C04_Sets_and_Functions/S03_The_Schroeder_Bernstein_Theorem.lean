import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

/- TEXT:
.. _the_schroeder_bernstein_theorem:

Schröder-Bernstein 定理
------------------------------

我们以一个初等但非平凡的集合论定理来结束本章。
设 :math:`\alpha` 和 :math:`\beta` 为集合。
（在我们的形式化中，它们实际上是类型。）
假设 :math:`f : \alpha → \beta` 和 :math:`g : \beta → \alpha`
都是单射。
直观上，这意味着 :math:`\alpha` 不大于 :math:`\beta`，反之亦然。
如果 :math:`\alpha` 和 :math:`\beta` 是有限的，这蕴含
它们具有相同的基数，这等价于说它们之间存在
一个双射。
在十九世纪，康托尔断言同样的结果即使在
:math:`\alpha` 和 :math:`\beta` 是无限的情况下也成立。
这最终由 Dedekind、Schröder 和 Bernstein
独立地证明。

我们的形式化将引入一些新方法，我们将在
后续章节中更详细地解释。
如果这里它们讲得太快，不必担心。
我们的目标是向你展示，你已经具备了为一个真正的数学结果
贡献形式化证明的技能。

要理解证明背后的思想，考虑映射 :math:`g`
在 :math:`\alpha` 中的像。
在该像上，:math:`g` 的逆是定义的，并且是与 :math:`\beta` 的
双射。

.. image:: /figures/schroeder_bernstein1.*
   :height: 150 px
   :alt: Schröder Bernstein 定理
   :align: center

问题在于这个双射不包含图中阴影区域，
如果 :math:`g` 不是满射，该区域非空。
或者，我们可以使用 :math:`f` 将整个
:math:`\alpha` 映射到 :math:`\beta`，
但此时的问题是如果 :math:`f` 不是满射，
它将遗漏 :math:`\beta` 的某些元素。

.. image:: /figures/schroeder_bernstein2.*
   :height: 150 px
   :alt: Schröder Bernstein 定理
   :align: center

但现在考虑复合 :math:`g \circ f` 从 :math:`\alpha` 到
自身。因为这个复合是单射，它在 :math:`\alpha` 和它的像之间
形成一个双射，产生 :math:`\alpha` 内部的一个缩小副本。

.. image:: /figures/schroeder_bernstein3.*
   :height: 150 px
   :alt: Schröder Bernstein 定理
   :align: center

这个复合将内部的阴影环映射到另一个这样的
集合，我们可以将其视为一个更小的同心阴影环，
以此类推。
这产生了一个
同心阴影环序列，其中每个环都与下一个环
成双射对应。
如果我们将每个环映射到下一个，并保持 :math:`\alpha` 的
非阴影部分不变，
我们就得到了 :math:`\alpha` 与 :math:`g` 的像之间的双射。
通过与 :math:`g^{-1}` 复合，这给出了所需的
:math:`\alpha` 与 :math:`\beta` 之间的双射。

我们可以更简单地描述这个双射。
令 :math:`A` 为阴影区域序列的并集，并
定义 :math:`h : \alpha \to \beta` 如下：

.. math::

  h(x) = \begin{cases}
    f(x) & \text{若 $x \in A$} \\
    g^{-1}(x) & \text{否则.}
  \end{cases}

换句话说，我们在阴影部分使用 :math:`f`，
在其他地方使用 :math:`g` 的逆。
得到的映射 :math:`h` 是单射，
因为每个分量都是单射，
且两个分量的像不相交。
要看到它是满射，
假设我们给定 :math:`\beta` 中的一个 :math:`y`，并
考虑 :math:`g(y)`。
如果 :math:`g(y)` 在某个阴影区域中，
它不可能在第一个环中，因此我们有 :math:`g(y) = g(f(x))`
对前一个环中的某个 :math:`x` 成立。
由 :math:`g` 的单射性，我们有 :math:`h(x) = f(x) = y`。
如果 :math:`g(y)` 不在阴影区域中，
则由 :math:`h` 的定义，我们有 :math:`h(g(y))= y`。
无论哪种情况，:math:`y` 都在 :math:`h` 的像中。

这个论证听起来应该是合理的，但细节是微妙的。
形式化这个证明不仅能提高我们对结果的信心，
还能帮助我们更好地理解它。
因为证明使用了经典逻辑，我们告诉 Lean 我们的定义
通常是不可计算的。
BOTH: -/
-- QUOTE:
noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]
-- QUOTE.

/- TEXT:
注解 ``[Nonempty β]`` 指定 ``β`` 是非空的。
我们使用它，因为我们将用来构造 :math:`g^{-1}` 的 Mathlib 原语
需要它。
定理中 :math:`\beta` 为空的情况是平凡的，
尽管形式化推广以覆盖那种情况
并不困难，我们就不费心了。
具体来说，我们需要假设 ``[Nonempty β]`` 来使用 Mathlib 中
定义的运算 ``invFun``。
给定 ``x : α``，``invFun g x`` 选择 ``x`` 在 ``β`` 中的一个原像
（如果存在的话），
否则返回 ``β`` 的任意元素。
函数 ``invFun g`` 在 ``g`` 是单射时总是左逆，
在 ``g`` 是满射时总是右逆。

-- LITERALINCLUDE: invFun g

我们如下定义对应于阴影区域并集的集合。

BOTH: -/
section
-- QUOTE:
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
-- QUOTE.

/- TEXT:
定义 ``sbAux`` 是一个*递归定义*的例子，
我们将在下一章中解释。
它定义了一个集合序列

.. math::

  S_0 &= α ∖ g(\beta) \\
  S_{n+1} &= g(f(S_n)).

定义 ``sbSet`` 对应于我们证明草图中
的集合 :math:`A = \bigcup_{n \in \mathbb{N}} S_n`。
上面描述的函数 :math:`h` 现在定义如下：
BOTH: -/
-- QUOTE:
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
-- QUOTE.

/- TEXT:
我们需要 :math:`g^{-1}` 的定义在 :math:`A` 的补集上
是右逆这一事实，
也就是说，在 :math:`\alpha` 的非阴影区域上。
这是因为最外层环 :math:`S_0` 等于
:math:`\alpha \setminus g(\beta)`，因此 :math:`A` 的补集
包含在 :math:`g(\beta)` 中。
因此，对于 :math:`A` 的补集中的每个 :math:`x`，
存在 :math:`y` 使得 :math:`g(y) = x`。
（由 :math:`g` 的单射性，这个 :math:`y` 是唯一的，
但下一个定理只说 ``invFun g x`` 返回某个 ``y``
使得 ``g y = x``。）

逐步执行下面的证明，确保你理解其中发生的事情，
并填补剩余的部分。
你需要在最后使用 ``invFun_eq``。
注意，用 ``sbAux`` 重写会将 ``sbAux f g 0``
替换为对应定义方程的右边。
BOTH: -/
-- QUOTE:
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact ⟨mem_univ _, hx⟩
-- BOTH:
  have : ∃ y, g y = x := by
/- EXAMPLES:
    sorry
  sorry
SOLUTIONS: -/
    simp at this
    assumption
  exact invFun_eq this
-- BOTH:
-- QUOTE.

/- TEXT:
现在我们转向 :math:`h` 是单射的证明。
非正式地，证明如下进行。
首先，假设 :math:`h(x_1) = h(x_2)`。
如果 :math:`x_1` 在 :math:`A` 中，则 :math:`h(x_1) = f(x_1)`，
我们可以如下证明 :math:`x_2` 在 :math:`A` 中。
如果不在，则我们有 :math:`h(x_2) = g^{-1}(x_2)`。
由 :math:`f(x_1) = h(x_1) = h(x_2)` 我们有 :math:`g(f(x_1)) = x_2`。
由 :math:`A` 的定义，因为 :math:`x_1` 在 :math:`A` 中，
:math:`x_2` 也在 :math:`A` 中，矛盾。
因此，如果 :math:`x_1` 在 :math:`A` 中，那么 :math:`x_2` 也在，
此时我们有 :math:`f(x_1) = h(x_1) = h(x_2) = f(x_2)`。
:math:`f` 的单射性然后蕴含 :math:`x_1 = x_2`。
对称论证表明如果 :math:`x_2` 在 :math:`A` 中，
那么 :math:`x_1` 也在，这同样蕴含 :math:`x_1 = x_2`。

唯一剩下的可能性是 :math:`x_1` 和 :math:`x_2`
都不在 :math:`A` 中。此时，我们有
:math:`g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)`。
对两边应用 :math:`g` 得到 :math:`x_1 = x_2`。

再次，我们鼓励你逐步执行以下证明，
看看该论证如何在 Lean 中展开。
看看你能否使用 ``sb_right_inv`` 完成证明。
BOTH: -/
-- QUOTE:
theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
/- EXAMPLES:
        sorry
SOLUTIONS: -/
        rw [hxeq, sb_right_inv f g x₂nA]
-- BOTH:
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
-- BOTH:
  push_neg at xA
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]
-- BOTH:
-- QUOTE.

/- TEXT:
证明引入了一些新策略。
首先，注意 ``set`` 策略，它引入缩写
``A`` 和 ``h`` 分别代表 ``sbSet f g`` 和 ``sb_fun f g``。
我们命名相应的定义等式 ``A_def`` 和 ``h_def``。
这些缩写是定义性的，也就是说，Lean 有时
会在需要时自动展开它们。
但不是总是如此；例如，在使用 ``rw`` 时，我们通常需要
显式使用 ``A_def`` 和 ``h_def``。
因此这些定义带来了一种权衡：它们可以使表达式更短
且更易读，但有时需要我们做更多工作。

一个更有趣的策略是 ``wlog`` 策略，它封装了
上述非正式证明中的对称论证。
我们现在不深入讨论它，但请注意它正好做了我们想要的。
如果你将鼠标悬停在此策略上，可以查看其文档。

满射性的论证甚至更容易。
给定 :math:`\beta` 中的 :math:`y`，
我们考虑两种情况，取决于 :math:`g(y)` 是否在 :math:`A` 中。
如果在，它不可能在 :math:`S_0` 中，即最外层环，
因为根据定义，那是与 :math:`g` 的像不相交的。
因此它是某个 :math:`S_{n+1}` 的元素，对某个 :math:`n`。
这意味着它具有形式 :math:`g(f(x))`，对于
:math:`S_n` 中的某个 :math:`x`。
由 :math:`g` 的单射性，我们有 :math:`f(x) = y`。
在 :math:`g(y)` 在 :math:`A` 的补集中的情况下，
我们立即有 :math:`h(g(y))= y`，证毕。

再次，我们鼓励你逐步执行证明并填补
缺失的部分。
策略 ``rcases n with _ | n`` 分拆 ``g y ∈ sbAux f g 0``
和 ``g y ∈ sbAux f g (n + 1)`` 的情况。
在两种情况下，调用带有 ``simp [sbAux]`` 的化简器
应用 ``sbAux`` 的对应定义方程。
BOTH: -/
-- QUOTE:
theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]
    apply hg hx

/- EXAMPLES:
  sorry
SOLUTIONS: -/
  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg
-- BOTH:
-- QUOTE.

end

/- TEXT:
我们现在可以将所有内容整合在一起。最终的陈述简短而优美，
证明使用了 ``Bijective h`` 展开为
``Injective h ∧ Surjective h`` 这一事实。
EXAMPLES: -/
-- QUOTE:
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
-- QUOTE.

-- Auxiliary information
section
variable (g : β → α) (x : α)

-- TAG: invFun g
#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)
-- TAG: end

end
