-- BOTH:
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

/- TEXT:
.. _sets:

集合
----

.. index:: set operations

若 ``α`` 是任意类型，则类型 ``Set α`` 由 ``α`` 的元素的集合组成。
该类型支持通常的集合论运算和关系。
例如，``s ⊆ t`` 表示 ``s`` 是 ``t`` 的子集，
``s ∩ t`` 表示 ``s`` 与 ``t`` 的交集，
``s ∪ t`` 表示它们的并集。
子集关系可以用 ``\ss`` 或 ``\sub`` 输入，
交集可以用 ``\i`` 或 ``\cap`` 输入，
并集可以用 ``\un`` 或 ``\cup`` 输入。
该库还定义了全集 ``univ``，
它包含类型 ``α`` 的所有元素，
以及空集 ``∅``，可以用 ``\empty`` 输入。
给定 ``x : α`` 和 ``s : Set α``，
表达式 ``x ∈ s`` 表示 ``x`` 是 ``s`` 的元素。
涉及集合成员关系的定理通常在名称中包含 ``mem``。
表达式 ``x ∉ s`` 是 ``¬ x ∈ s`` 的简写。
你可以用 ``\in`` 或 ``\mem`` 输入 ``∈``，用 ``\notin`` 输入 ``∉``。

.. index:: simp, tactics ; simp

证明集合相关命题的一种方法是使用 ``rw``
或化简器展开定义。
在下面的第二个例子中，我们使用 ``simp only``
告诉化简器只使用我们给出的恒等式列表，
而不是使用其完整的恒等式数据库。
与 ``rw`` 不同，``simp`` 可以在全称量词或存在量词
内部进行化简。
如果你逐步执行证明，
你可以看到这些命令的效果。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*}
variable (s t u : Set α)
open Set

-- EXAMPLES:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
-- QUOTE.

/- TEXT:
在这个例子中，我们打开 ``Set`` 命名空间以便
使用较短名称的定理。
但事实上，我们可以完全删除 ``rw`` 和 ``simp`` 的调用：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
-- QUOTE.

/- TEXT:
这里发生的现象称为*定义归约*：
为了使 ``intro`` 命令和匿名构造子有意义，
Lean 被迫展开相关定义。
下面的例子也展示了这个现象：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
-- QUOTE.

/- TEXT:
要处理并集，我们可以使用 ``Set.union_def`` 和 ``Set.mem_union``。
由于 ``x ∈ s ∪ t`` 展开为 ``x ∈ s ∨ x ∈ t``，
我们也可以使用 ``cases`` 策略强制进行定义归约。
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
由于交集的结合性比并集更强，
表达式 ``(s ∩ t) ∪ (s ∩ u)`` 中的括号
不是必需的，但它们使表达式的含义更清晰。
下面是同一事实的更短证明：
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
作为练习，请尝试证明另一个包含方向：
BOTH: -/
-- QUOTE:
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.

-- BOTH:
/- TEXT:
知道以下内容可能会有所帮助：在使用 ``rintro`` 时，
有时我们需要在析取模式 ``h1 | h2`` 周围使用括号，
以便 Lean 能正确解析它。

该库还定义了集合差，``s \ t``，
其中反斜杠是一个特殊的 Unicode 字符，
通过 ``\\`` 输入。
表达式 ``x ∈ s \ t`` 展开为 ``x ∈ s ∧ x ∉ t``。
（``∉`` 可以通过 ``\notin`` 输入。）
它可以使用 ``Set.diff_eq`` 和 ``dsimp``
或 ``Set.mem_diff`` 手动重写，
但下面两个同一包含关系的证明
展示了如何避免使用它们。
TEXT. -/
-- QUOTE:
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction
-- QUOTE.

/- TEXT:
作为练习，请证明反向包含：
BOTH: -/
-- QUOTE:
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)
-- QUOTE.

-- BOTH:
/- TEXT:
要证明两个集合相等，
只需证明其中一个集合的每个元素也是
另一个集合的元素。
这个原理被称为"外延性"，
毫不奇怪，
``ext`` 策略可以处理它。
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
同样，删除 ``simp only [mem_inter_iff]`` 这一行
不会损害证明。
事实上，如果你喜欢难以理解的证明项，
下面的一行证明适合你：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩
-- QUOTE.

/- TEXT:
这里是一个更短的证明，
使用化简器：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]
-- QUOTE.

/- TEXT:
使用 ``ext`` 的另一种方法是使用
定理 ``Subset.antisymm``，
它允许我们通过证明 ``s ⊆ t`` 和 ``t ⊆ s``
来证明集合之间的等式 ``s = t``。
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
尝试完成以下证明项：
BOTH: -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
/- EXAMPLES:
    Subset.antisymm sorry sorry
SOLUTIONS: -/
    Subset.antisymm
    (fun _x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun _x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩
-- QUOTE.

-- BOTH:
/- TEXT:
请记住，你可以用下划线替换 `sorry`，
当你将鼠标悬停在其上时，
Lean 会显示它在该位置期望的内容。

以下是一些你可能喜欢的集合论恒等式：
TEXT. -/
-- QUOTE:
example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  · intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    · constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  · right; use xt; intro xs
    apply nxst
    constructor <;> assumption

/- TEXT:
在表示集合时，
以下是底层发生的事情。
在类型论中，类型 ``α`` 上的一个*属性*或*谓词*
只是一个函数 ``P : α → Prop``。
这有道理：
给定 ``a : α``，``P a`` 就是 ``P`` 对 ``a`` 成立
的命题。
在该库中，``Set α`` 被定义为 ``α → Prop``，而 ``x ∈ s`` 被定义为 ``s x``。
换句话说，集合实际上是属性，被当作对象来处理。

该库还定义了集合构造符号。
表达式 ``{ y | P y }`` 展开为 ``(fun y ↦ P y)``，
因此 ``x ∈ { y | P y }`` 归约为 ``P x``。
因此我们可以将偶数的性质转化为偶数集合：
TEXT. -/
-- QUOTE:
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em
-- QUOTE.

/- TEXT:
你应该逐步执行这个证明，确保
你理解其中发生的事情。
注意我们告诉化简器*不要*使用引理
``Nat.not_even_iff``，因为我们想在我们的目标中
保留 ``¬ Even n``。
尝试删除 ``rw [evens, odds]`` 这一行
并确认证明仍然有效。

事实上，集合构造符号被用来定义

- ``s ∩ t`` 为 ``{x | x ∈ s ∧ x ∈ t}``，
- ``s ∪ t`` 为 ``{x | x ∈ s ∨ x ∈ t}``，
- ``∅`` 为 ``{x | False}``，以及
- ``univ`` 为 ``{x | True}``。

我们经常需要显式地指明 ``∅`` 和 ``univ`` 的类型，
因为 Lean 难以猜测我们指的是哪一个。
下面的例子展示了 Lean 在需要时如何展开
后两个定义。在第二个例子中，
``trivial`` 是该库中 ``True`` 的规范证明。
TEXT. -/
-- QUOTE:
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial
-- QUOTE.

/- TEXT:
作为练习，请证明以下包含关系。
使用 ``intro n`` 展开子集的定义，
并使用化简器将集合论构造
归约为逻辑。
我们还建议使用定理
``Nat.Prime.eq_two_or_odd`` 和 ``Nat.odd_iff``。
TEXT. -/
-- QUOTE:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime n_gt
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    linarith
  · rw [Nat.odd_iff, h]

/- TEXT:
注意：该库有多个 ``Prime`` 谓词的版本，
这可能会有些令人困惑。
最一般的版本在任何带有零元素的交换幺半群中都有意义。
谓词 ``Nat.Prime`` 是专门针对自然数的。
幸运的是，有一个定理说在特定情况下，
这两个概念是一致的，因此你总是可以将一个重写为另一个。
TEXT. -/
-- QUOTE:
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
-- QUOTE.

/- TEXT:
.. index:: rwa, tactics ; rwa

`rwa` 策略在重写后跟随 assumption 策略。
TEXT. -/
-- QUOTE:
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]
-- QUOTE.

-- BOTH:
end

/- TEXT:
.. index:: bounded quantifiers

Lean 引入了符号 ``∀ x ∈ s, ...``，
"对于 ``s`` 中的每个 ``x``，..."
作为 ``∀ x, x ∈ s → ...`` 的简写。
它还引入了符号 ``∃ x ∈ s, ...,``
"存在 ``s`` 中的 ``x`` 使得 ..."
这些有时被称为*有界量词*，
因为这种构造用于将其作用范围限制
到集合 ``s``。
因此，该库中使用它们的定理
通常在名称中包含 ``ball`` 或 ``bex``。
定理 ``bex_def`` 断言 ``∃ x ∈ s, ...`` 等价于
``∃ x, x ∈ s ∧ ...,``
但当它们与 ``rintro``、``use``
和匿名构造子一起使用时，
这两种表达式的行为大致相同。
因此，我们通常不需要使用 ``bex_def``
来显式地转换它们。
以下是一些使用示例：
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable (s t : Set ℕ)

-- EXAMPLES:
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs
-- QUOTE.

/- TEXT:
看看你能否证明以下稍有不同的变体：
TEXT. -/
-- QUOTE:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end
-- QUOTE.

-- SOLUTIONS:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

-- BOTH:
end

/- TEXT:
索引并集和索引交集是
另一个重要的集合论构造。
我们可以将 ``α`` 的元素集合的序列
:math:`A_0, A_1, A_2, \ldots`
建模为函数 ``A : ℕ → Set α``，
此时 ``⋃ i, A i`` 表示它们的并集，
而 ``⋂ i, A i`` 表示它们的交集。
这里自然数没有什么特别之处，
因此 ``ℕ`` 可以被任何用于索引集合的类型 ``I``
替换。
以下展示了它们的使用。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

-- EXAMPLES:
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i
-- QUOTE.

/- TEXT:
在索引并集或索引交集中通常需要括号，
因为与量词一样，
绑定变量的作用范围尽可能远地延伸。

尝试证明以下恒等式。
一个方向需要经典逻辑！
我们建议在证明的适当位置
使用 ``by_cases xs : x ∈ s``。
TEXT. -/
-- QUOTE:

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

/- TEXT:
Mathlib 也有有界并集和有界交集，
它们类似于有界量词。
你可以用 ``mem_iUnion₂`` 和 ``mem_iInter₂``
来展开它们的含义。
如下面的例子所示，
Lean 的化简器也会进行这些替换。
TEXT. -/
-- QUOTE:
-- BOTH:
def primes : Set ℕ :=
  { x | Nat.Prime x }

-- EXAMPLES:
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd
-- QUOTE.

/- TEXT:
尝试解决以下类似的例子。
如果你开始输入 ``eq_univ``，
Tab 补全会告诉你 ``apply eq_univ_of_forall``
是开始证明的好方法。
我们还建议使用定理 ``Nat.exists_infinite_primes``。
TEXT. -/
-- QUOTE:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, pge, primep⟩
  use p, primep

-- BOTH:
end

/- TEXT:
给定一个集合的集合 ``s : Set (Set α)``，
它们的并集 ``⋃₀ s`` 的类型为 ``Set α``，
定义为 ``{x | ∃ t ∈ s, x ∈ t}``。
类似地，它们的交集 ``⋂₀ s`` 定义为
``{x | ∀ t ∈ s, x ∈ t}``。
这些运算分别称为 ``sUnion`` 和 ``sInter``。
以下例子展示了它们与有界并集
和有界交集的关系。
TEXT. -/
section

open Set

-- QUOTE:
variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl
-- QUOTE.

end

/- TEXT:
在该库中，这些恒等式被称为
``sUnion_eq_biUnion`` 和 ``sInter_eq_biInter``。
TEXT. -/
