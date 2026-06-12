import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction

/- TEXT:

.. _more_induction:

更多归纳
--------------

在 :numref:`section_induction_and_recursion` 中，我们看到了如何
通过对自然数的递归来定义阶乘函数。
EXAMPLES: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
我们还看到如何使用 ``induction'`` 策略证明定理。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
``induction`` 策略（不带撇号）允许更结构化的语法。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : 0 < fac n := by
  induction n
  case zero =>
    rw [fac]
    exact zero_lt_one
  case succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih

example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    rw [fac]
    exact zero_lt_one
  | succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
像往常一样，你可以将鼠标悬停在 ``induction`` 关键字上以阅读文档。
情况的名称 ``zero`` 和 ``succ`` 取自类型 ``ℕ`` 的定义。
注意 ``succ`` 情况允许你为归纳变量和归纳假设
选择任何你喜欢的名称，这里是 ``n`` 和 ``ih``。
你甚至可以用定义递归函数时使用的相同记号来证明定理。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos' : ∀ n, 0 < fac n
  | 0 => by
    rw [fac]
    exact zero_lt_one
  | n + 1 => by
    rw [fac]
    exact mul_pos n.succ_pos (fac_pos' n)
-- QUOTE.

/- TEXT:
还要注意缺少了 ``:=``，冒号后的 ``∀ n``，每种情况中的 ``by`` 关键字，
以及归纳调用 ``fac_pos' n``。
就好像定理是关于 ``n`` 的递归函数，在归纳步骤中我们进行了
递归调用。

这种定义风格非常灵活。
Lean 的设计者建立了精心设计的定义递归函数的方法，这些
扩展到了通过归纳进行证明。
例如，我们可以定义具有多个基础情况的斐波那契函数。
BOTH: -/
-- QUOTE:
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- QUOTE.

/- TEXT:
``@[simp]`` 注解意味着化简器将使用定义方程。
你也可以通过写 ``rw [fib]`` 来应用它们。
在下面，给 ``n + 2`` 情况一个名称将很有用。
BOTH: -/
-- QUOTE:
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

-- EXAMPLES:
example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]
-- QUOTE.

/- TEXT:
使用 Lean 的递归函数记号，你可以通过对反映 ``fib`` 的递归定义的
自然数进行归纳来进行证明。
以下例子用黄金分割率 ``φ`` 及其共轭 ``φ'``
给出了第 n 个斐波那契数的显式公式。
我们必须告诉 Lean 我们不期望我们的定义生成代码，因为
实数上的算术运算是不可计算的。

我们将使用 `grind` 策略进行计算，告诉它使用 `phi` 和 `phi'` 的定义
以及归纳假设 `fib_eq n` 和 `fib_eq (n+1)`。
EXAMPLES: -/
-- QUOTE:
noncomputable section

def phi  : ℝ := (1 + √5) / 2
def phi' : ℝ := (1 - √5) / 2

theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
  | 0   => by simp
  | 1   => by unfold fib; grind [phi, phi']
  | n+2 => by unfold fib; simp; grind [fib_eq n, fib_eq (n+1), phi, phi']

end
-- QUOTE.

/- TEXT:
涉及斐波那契函数的归纳证明不一定是那种形式。
下面我们复现了 ``Mathlib`` 中连续斐波那契数互质的证明。
EXAMPLES: -/
-- QUOTE:
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
-- QUOTE.

/- TEXT:
使用 Lean 的计算解释，我们可以计算斐波那契数。
EXAMPLES: -/
-- QUOTE:
#eval fib 6
#eval List.range 20 |>.map fib
-- QUOTE.

/- TEXT:
``fib`` 的直接实现在计算上是低效的。事实上，它的运行
时间关于其参数是指数级的。（你应该思考为什么。）
在 Lean 中，我们可以实现以下尾递归版本，其运行时间关于 ``n`` 是线性的，
并证明它计算相同的函数。
EXAMPLES: -/
-- QUOTE:
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux
  | 0,   x, _ => x
  | n+1, x, y => aux n y (x + y)

theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl

#eval fib' 10000
-- QUOTE.

/- TEXT:
注意 ``fib'.aux_eq`` 证明中的 ``generalizing`` 关键字。
它用于在归纳假设之前插入一个 ``∀ m``，使得在归纳步骤
中，``m`` 可以取不同的值。
你可以逐步执行证明并检查，在这种情况下，量词需要在
归纳步骤中被实例化为 ``m + 1``。

还要注意这里使用 ``erw``（扩展重写）而不是 ``rw``。
这样做是因为要重写目标 ``fib'.aux_eq``，需要将 ``fib 0`` 和 ``fib 1``
分别归约为 ``0`` 和 ``1``。
策略 ``erw`` 在展开定义以匹配参数方面比 ``rw`` 更激进。
这并不总是一个好主意；在某些情况下它可能浪费大量时间，因此请
谨慎使用 ``erw``。

这是另一个使用 ``generalizing`` 关键字的例子，用于证明
``Mathlib`` 中另一个恒等式的证明。
该恒等式的非正式证明可以在 `这里 <https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers>`_ 找到。
我们提供了两个形式化证明的变体。
BOTH: -/
-- QUOTE:
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

-- EXAMPLES:
theorem fib_add' : ∀ m n, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  | _, 0     => by simp
  | m, n + 1 => by
    have := fib_add' (m + 1) n
    rw [add_assoc m 1 n, add_comm 1 n] at this
    simp only [fib_add_two, this]
    ring
-- QUOTE.

/- TEXT:
作为练习，使用 ``fib_add`` 来证明以下内容。
BOTH: -/
-- QUOTE:
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [two_mul, fib_add, pow_two, pow_two]
-- QUOTE.

/- TEXT:
Lean 定义递归函数的机制足够灵活，允许任意的
递归调用，只要参数的复杂性按照某个
良基测度递减。
在下一个例子中，我们证明每个不是 1 的自然数 ``n`` 都有一个素因子，
使用的事实是如果 ``n`` 是非零且非素数，它有一个更小的因子。
（你可以检查 Mathlib 在 ``Nat`` 命名空间中有一个相同名称的定理，
尽管它的证明与我们这里给出的不同。）
EXAMPLES: -/
-- QUOTE:
#check (@Nat.not_prime_iff_exists_dvd_lt :
  ∀ {n : ℕ}, 2 ≤ n → (¬Nat.Prime n ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    have hn : n + 2 ≠ 1 := by omega
    simp only [Ne, not_false_iff, true_iff, hn]
    by_cases h : Nat.Prime (n + 2)
    · use n + 2, h
    · have : 2 ≤ n + 2 := by omega
      rw [Nat.not_prime_iff_exists_dvd_lt this] at h
      rcases h with ⟨m, mdvdn, mge2, -⟩
      have : m ≠ 1 := by omega
      rw [ne_one_iff_exists_prime_dvd] at this
      rcases this with ⟨p, primep, pdvdm⟩
      use p, primep
      exact pdvdm.trans mdvdn
-- QUOTE.

/- TEXT:
行 ``rw [ne_one_iff_exists_prime_dvd] at this`` 就像一个魔术：我们正在
使用我们正在证明的定理本身来证明它。
使其有效的原因是归纳调用是在 ``m`` 处实例化的，
当前情况是 ``n + 2``，而上下文中有 ``m < n + 2``。
Lean 能够找到这个假设并使用它来证明归纳是良基的。
Lean 很擅长找出什么在递减；在这种情况下，定理陈述中 ``n`` 的选择
和小于关系是显然的。
在更复杂的情况下，Lean 提供了显式提供此信息的机制。
参见 Lean 参考手册中关于 `well-founded recursion <https://lean-lang.org/doc/reference/latest//Definitions/Recursive-Definitions/#well-founded-recursion>`_ 的章节。

有时，在证明中，你需要根据自然数 ``n`` 是零还是后继
来拆分情况，而不需要在后继情况中具有归纳假设。
为此，你可以使用 ``cases`` 和 ``rcases`` 策略。
EXAMPLES: -/
-- QUOTE:
theorem zero_lt_of_mul_eq_one (m n : ℕ) : n * m = 1 → 0 < n ∧ 0 < m := by
  cases n <;> cases m <;> simp

example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  rcases m with (_ | m); simp
  rcases n with (_ | n) <;> simp
-- QUOTE.

/- TEXT:
这是一个有用的技巧。
通常你有一个关于自然数 ``n`` 的定理，其中零情况很简单。
如果你对 ``n`` 拆分并快速处理零情况，你就剩下原始目标，
但 ``n`` 被替换为 ``n + 1``。
EXAMPLES: -/
