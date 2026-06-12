import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

/- TEXT:
.. _section_infinitely_many_primes:

无穷多个素数
----------------------

让我们继续我们对归纳与递归的探索，使用另一个
数学标准：存在无穷多个素数的证明。
一种表述方式是：对于每个自然数
:math:`n`，存在一个大于 :math:`n` 的素数。
为证明这一点，令 :math:`p` 为 :math:`n! + 1` 的任意素因子。
如果 :math:`p` 小于或等于 :math:`n`，它整除 :math:`n!`。
因为它也整除 :math:`n! + 1`，它整除 1，矛盾。
因此 :math:`p` 大于 :math:`n`。

要形式化这个证明，我们需要证明任何大于或等于 2
的数都有素因子。
为此，我们需要证明任何不等于 0 或 1 的自然数
都大于或等于 2。
而这将我们带到形式化的一个古怪特点：
通常是像这样的平凡陈述在形式化时
最令人烦恼。
在这里我们考虑几种方法。

首先，我们可以使用 ``cases`` 策略和后继函数
在自然数的序上保持性质的事实。
BOTH: -/
-- QUOTE:
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le
-- QUOTE.

/- TEXT:
另一种策略是使用策略 ``interval_cases``，
当涉及的变量包含在自然数或整数
的区间中时，它会自动将目标拆分为
各种情况。
记住你可以将鼠标悬停在其上查看其文档。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction
-- QUOTE.

/- TEXT:
.. index:: decide, tactics ; decide

回忆 ``interval_cases m`` 后面的分号意味着
下一个策略被应用到它生成的每种情况。
另一个选择是使用策略 ``decide``，它尝试
寻找一个决策过程来解决问题。
Lean 知道你可以通过决定有限多个实例
来决定一个以有界量词 ``∀ x, x < n → ...`` 或 ``∃ x, x < n ∧ ...``
开头的陈述的真值。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide
-- QUOTE.

/- TEXT:
有了定理 ``two_le`` 在手，让我们从证明每个
大于 2 的自然数都有一个素因子开始。
Mathlib 包含一个函数 ``Nat.minFac``，
它返回最小的素因子，
但为了学习库的新部分，
我们将避免使用它，直接证明该定理。

这里，普通归纳不够。
我们想使用*强归纳*，它允许我们通过证明
对于每个数 :math:`n`，如果 :math:`P` 对所有小于 :math:`n` 的值
成立，那么它在 :math:`n` 处也成立，来证明
每个自然数 :math:`n` 具有性质 :math:`P`。
在 Lean 中，这个原理被称为 ``Nat.strong_induction_on``，
我们可以使用 ``using`` 关键字告诉归纳策略
使用它。
注意当我们这样做时，没有基础情况；它被
一般归纳步骤所包含。

论证如下。假设 :math:`n ≥ 2`，
如果 :math:`n` 是素数，我们完成了。如果不是，
那么根据素数定义的一个刻画，
它有一个非平凡因子 :math:`m`，
我们可以对该因子应用归纳假设。
逐步执行下一个证明，看看这是如何展开的。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
-- QUOTE.

/- TEXT:
现在我们可以证明我们定理的如下表述。
看看你能否填补草稿。
你可以使用 ``Nat.factorial_pos``、``Nat.dvd_factorial``
和 ``Nat.dvd_sub'``。
BOTH: -/
-- QUOTE:
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_factorial
    apply pp.pos
    linarith
-- BOTH:
  have : p ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub pdvd this
    simp
-- BOTH:
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
让我们考虑上述证明的一个变体，其中
不使用阶乘函数，
而是假设给定一个有限集
:math:`\{ p_1, \ldots, p_n \}` 并考虑
:math:`\prod_{i = 1}^n p_i + 1` 的一个素因子。
该素因子必须不同于每个
:math:`p_i`，表明不存在包含所有素数的
有限集。

形式化这个论证需要我们推理有限集。
在 Lean 中，对于任何类型 ``α``，类型 ``Finset α``
表示类型为 ``α`` 的元素的有限集。
在计算上推理有限集需要有一个
测试 ``α`` 上相等性的过程，这就是为什么下面的代码段
包含假设 ``[DecidableEq α]``。
对于像 ``ℕ``、``ℤ`` 和 ``ℚ`` 这样的具体数据类型，
该假设会自动满足。当推理
实数时，可以通过使用经典逻辑
并放弃计算解释来满足它。

我们使用命令 ``open Finset`` 来使用
更短的相关定理名称。与集合的情况不同，
大多数涉及有限集的等价关系在定义上不成立，
因此需要使用像
``Finset.subset_iff``、``Finset.mem_union``、``Finset.mem_inter``
和 ``Finset.mem_sdiff`` 这样的等价关系来手动展开。``ext`` 策略仍然可以用来
通过证明两个有限集的一个中的
每个元素是另一个的元素来显示它们相等。
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end
-- QUOTE.

/- TEXT:
我们使用了一个新技巧：``tauto`` 策略（以及加强版
``tauto!``，它使用经典逻辑）可以用来
处理命题重言式。看看你能否使用
这些方法来证明下面的两个例子。
BOTH: -/
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

-- QUOTE:
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_inter, mem_union, mem_union, mem_union, mem_inter]
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

-- BOTH:
example : (r \ s) \ t = r \ (s ∪ t) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_sdiff, mem_sdiff, mem_sdiff, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto
-- QUOTE.
-- BOTH:

end

/- TEXT:
定理 ``Finset.dvd_prod_of_mem`` 告诉我们，如果
``n`` 是有限集 ``s`` 的一个元素，那么 ``n`` 整除
``∏ i ∈ s, i``。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h
-- QUOTE.

/- TEXT:
我们还需要知道在 ``n`` 是素数且 ``s`` 是素数集合的
情况下，反过来也成立。
要展示这一点，我们需要以下引理，你应该
能够使用定理 ``Nat.Prime.eq_one_or_self_of_dvd`` 来证明它。
BOTH: -/
-- QUOTE:
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  cases prime_q.eq_one_or_self_of_dvd _ h
  · linarith [prime_p.two_le]
  assumption
-- QUOTE.
-- BOTH:

/- TEXT:
我们可以使用这个引理来证明：如果一个素数 ``p`` 整除一个有限
素数集的乘积，那么它等于其中之一。
Mathlib 提供了一个有用的有限集归纳原理：
要证明一个性质对任意有限集 ``s`` 成立，
证明它对空集成立，并证明当添加一个
不在 ``s`` 中的新元素 ``a ∉ s`` 时它被保持。
该原理被称为 ``Finset.induction_on``。
当我们告诉归纳策略使用它时，我们也可以指定名称
``a`` 和 ``s``，归纳步骤中假设 ``a ∉ s`` 的名称，
以及归纳假设的名称。
表达式 ``Finset.insert a s`` 表示 ``s`` 与单元素集 ``a`` 的并集。
恒等式 ``Finset.prod_empty`` 和 ``Finset.prod_insert`` 然后提供了
乘积的相关重写规则。
在下面的证明中，第一个 ``simp`` 应用了 ``Finset.prod_empty``。
逐步执行证明的开头，看看归纳如何展开，
然后完成它。
BOTH: -/
-- QUOTE:
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rcases h₁ with h₁ | h₁
  · left
    exact prime_p.eq_of_dvd_of_prime h₀.1 h₁
  right
  exact ih h₀.2 h₁

-- BOTH:
-- QUOTE.
/- TEXT:
我们还需要有限集的最后一个性质。
给定一个元素 ``s : Set α`` 和一个 ``α`` 上的谓词
``P``，在 :numref:`Chapter %s <sets_and_functions>` 中
我们写了 ``{ x ∈ s | P x }`` 表示 ``s`` 中
满足 ``P`` 的元素的集合。
给定 ``s : Finset α``，
类似的概念写作 ``s.filter P``。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter
-- QUOTE.

/- TEXT:
现在我们证明存在无穷多个素数的另一种表述，
即给定任何 ``s : Finset ℕ``，存在一个素数 ``p`` 不是
``s`` 的元素。
为了推导矛盾，我们假设所有素数都在 ``s`` 中，然后
缩减到仅包含所有素数的集合 ``s'``。
取该集合的乘积，加一，并找到结果的一个
素因子，
导致我们正在寻找的矛盾。
看看你能否完成下面的草稿。
在第一个 ``have`` 的证明中，你可以使用 ``Finset.prod_pos``。
BOTH: -/
-- QUOTE:
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_prod_of_mem
    rw [mem_s']
    apply pp
-- BOTH:
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
我们因此看到了两种表述存在无穷多个素数的方式：
说它们不被任何 ``n`` 所界定，以及说它们
不被包含在任何有限集 ``s`` 中。
下面的两个证明表明这些表述是等价的。
在第二个中，为了形成 ``s.filter Q``，我们必须假设存在
一个决定 ``Q`` 是否成立的过程。Lean 知道
对 ``Nat.Prime`` 存在一个过程。通常，如果我们通过写
``open Classical`` 使用经典逻辑，
我们可以免除这个假设。

在 Mathlib 中，``Finset.sup s f`` 表示 ``f x`` 在 ``x`` 取遍
``s`` 时的上确界，当 ``s`` 为空且
``f`` 的上域为 ``ℕ`` 时返回 ``0``。在第一个证明中，我们使用 ``s.sup id``，
其中 ``id`` 是恒等函数，来引用 ``s`` 中的最大值。
BOTH: -/
-- QUOTE:
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simpa using hn k
-- QUOTE.

/- TEXT:
我们第二个证明存在无穷多个素数的一个小变体
表明存在无穷多个模 4 余 3 的素数。
论证如下。
首先，注意如果两个数 :math:`m` 和 :math:`n` 的乘积
模 4 等于 3，那么这两个数之一模 4 余 3。
毕竟，两者都必须是奇数，如果它们都模 4 余 1，
那么它们的乘积也是。
我们可以用这个观察来证明如果某个大于 2 的数
模 4 余 3，
那么该数有一个也模 4 余 3 的素因子。

现在假设只有有限多个模 4 余 3 的素数，
比如说 :math:`p_1, \ldots, p_k`。
不失一般性，我们可以假设 :math:`p_1 = 3`。
考虑乘积 :math:`4 \prod_{i = 2}^k p_i + 3`。
容易看出它模 4 等于 3，因此它有一个
模 4 余 3 的素因子 :math:`p`。
不可能有 :math:`p = 3`；因为 :math:`p`
整除 :math:`4 \prod_{i = 2}^k p_i + 3`，如果 :math:`p`
等于 3，那么它也会整除 :math:`\prod_{i = 2}^k p_i`，
这蕴含 :math:`p` 等于
某个 :math:`p_i`（:math:`i = 2, \ldots, k`）；
而我们已经从列表中排除了 3。
因此 :math:`p` 必须是其他元素 :math:`p_i` 之一。
但在这种情况下，:math:`p` 整除 :math:`4 \prod_{i = 2}^k p_i`
从而整除 3，这与它不是 3 的事实矛盾。

在 Lean 中，记号 ``n % m``，读作"``n`` 模 ``m``"，"
表示 ``n`` 除以 ``m`` 的余数。
EXAMPLES: -/
-- QUOTE:
example : 27 % 4 = 3 := by norm_num
-- QUOTE.

/- TEXT:
然后，我们可以将陈述"``n`` 模 4 余 3"
表示为 ``n % 4 = 3``。下面的例子和定理总结了
我们将在下面需要使用的关于这个函数的事实。
第一个命名定理是另一种通过少量情况
进行推理的说明。
在第二个命名定理中，记住分号意味着
后续的策略块被应用到前一个策略
创建的所有目标。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

-- BOTH:
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
-- QUOTE.

/- TEXT:
我们还需要以下事实，它说如果
``m`` 是 ``n`` 的一个非平凡因子，那么 ``n / m`` 也是。
看看你能否使用 ``Nat.div_dvd_of_dvd`` 和 ``Nat.div_lt_self``
来完成证明。
BOTH: -/
-- QUOTE:
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁
-- QUOTE.

-- BOTH:
/- TEXT:
现在将所有片段组合在一起，证明任何
模 4 余 3 的数都有一个具有相同
性质的素因子。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
/- EXAMPLES:
  . sorry
  . sorry
SOLUTIONS: -/
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

-- BOTH:
-- QUOTE.
/- TEXT:
我们到了最后阶段。给定一个素数集合 ``s``，
我们需要讨论从该集合中移除 3 的结果
（如果它存在）。函数 ``Finset.erase`` 处理这一点。
EXAMPLES: -/
-- QUOTE:
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
-- QUOTE.

/- TEXT:
现在我们已经准备好证明存在无穷多个
模 4 余 3 的素数。
填补下面缺失的部分。
我们的解在过程中使用了 ``Nat.dvd_add_iff_left`` 和 ``Nat.dvd_sub'``。
BOTH: -/
-- QUOTE:
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [add_comm, Nat.add_mul_mod_self_left]
-- BOTH:
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [← hs p]
    exact ⟨pp, p4eq⟩
-- BOTH:
  have pne3 : p ≠ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro peq
    rw [peq, ← Nat.dvd_add_iff_left (dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro n
      simp [← hs n]
      tauto
    simp at this
-- BOTH:
  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_trans _ (dvd_mul_left _ _)
    apply dvd_prod_of_mem
    simp
    constructor <;> assumption
-- BOTH:
  have : p ∣ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub pdvd this
    simp
-- BOTH:
  have : p = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply pp.eq_of_dvd_of_prime Nat.prime_three this
-- BOTH:
  contradiction
-- QUOTE.

/- TEXT:
如果你设法完成了证明，恭喜！这是一个严肃的
形式化成就。
TEXT. -/
-- OMIT:
/-
Later:
o fibonacci numbers
o binomial coefficients

(The former is a good example of having more than one base case.)

TODO: mention ``local attribute`` at some point.
-/
