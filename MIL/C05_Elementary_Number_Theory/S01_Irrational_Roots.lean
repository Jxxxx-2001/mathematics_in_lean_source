import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
/- OMIT:
-- fix this.
-- import Mathlib.Data.Real.Irrational
BOTH: -/

/- TEXT:
.. _section_irrational_roots:

无理根
----------------

让我们从一个古希腊人已知的事实开始，即
2 的平方根是无理数。
如果我们假设相反，
我们可以将 :math:`\sqrt{2} = a / b` 写成一个
最简分数。两边平方得到 :math:`a^2 = 2 b^2`，
这意味着 :math:`a` 是偶数。
如果我们写出 :math:`a = 2c`，那么我们得到 :math:`4c^2 = 2 b^2`
从而 :math:`b^2 = 2 c^2`。
这意味着 :math:`b` 也是偶数，与
我们假设 :math:`a / b` 已化到最简
的事实矛盾。

说 :math:`a / b` 是最简分数意味着
:math:`a` 和 :math:`b` 没有任何公因子，
也就是说，它们是*互质*的。
Mathlib 定义谓词 ``Nat.Coprime m n`` 为 ``Nat.gcd m n = 1``。
使用 Lean 的匿名投影记号，如果 ``s`` 和 ``t`` 是
类型为 ``Nat`` 的表达式，我们可以写 ``s.Coprime t`` 而不是
``Nat.Coprime s t``，对 ``Nat.gcd`` 类似。
像往常一样，Lean 在需要时通常会
自动展开 ``Nat.Coprime`` 的定义，
但我们也可以通过用标识符 ``Nat.Coprime`` 重写或化简
来手动进行。
``norm_num`` 策略足够聪明，可以计算具体的值。
EXAMPLES: -/
-- QUOTE:
#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num
-- QUOTE.

/- TEXT:
我们已经在 :numref:`more_on_order_and_divisibility` 中
遇到过 ``gcd`` 函数。
也有一个整数版本的 ``gcd``；
我们将在下面回到不同数系之间关系的
讨论。
甚至还有通用的 ``gcd`` 函数和通用的
``Prime`` 和 ``Coprime`` 概念，
它们在一般的代数结构类中都有意义。
我们将在下一章中理解 Lean 如何管理这种一般性。
同时，在本节中，我们将把注意力限制在
自然数上。

我们还需要素数 ``Nat.Prime`` 的概念。
定理 ``Nat.prime_def_lt`` 提供了一个熟悉的刻画，
而 ``Nat.Prime.eq_one_or_self_of_dvd`` 提供了另一个。
EXAMPLES: -/
-- QUOTE:
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
-- QUOTE.

/- TEXT:
在自然数中，素数具有不能写成非平凡因子
的乘积的性质。
在更广泛的数学背景中，一个环中具有此性质的元素
被称为*不可约*元素。
如果一个环的元素每当整除一个乘积时，
它就整除其中一个因子，则该元素被称为*素*元素。
自然数的一个重要性质是
在这种设定中这两个概念是一致的，
从而产生了定理 ``Nat.Prime.dvd_mul``。

我们可以用这个事实来建立上面论证中的
一个关键性质：
如果一个数的平方是偶数，那么该数也是偶数。
Mathlib 在 ``Algebra.Group.Even`` 中定义了谓词 ``Even``，
但出于下面将变得清楚的原因，
我们将简单地使用 ``2 ∣ m`` 来表达 ``m`` 是偶数。
EXAMPLES: -/
-- QUOTE:
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

-- BOTH:
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

-- EXAMPLES:
example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- QUOTE.

/- TEXT:
随着我们的进行，你将需要熟练地找到你需要的
事实。
记住，如果你能猜出名称的前缀并且
你已经导入了相关的库，
你可以使用 Tab 补全（有时用 ``ctrl-tab``）来找到
你要找的东西。
你可以在任何标识符上使用 ``ctrl-click`` 跳转到
它被定义的文件，这使你能够浏览附近的定义和定理。
你也可以使用
`Lean 社区网页 <https://leanprover-community.github.io/>`_ 上的搜索引擎，
如果所有方法都失败了，
不要犹豫在
`Zulip <https://leanprover.zulipchat.com/>`_ 上提问。
EXAMPLES: -/
-- QUOTE:
example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h
-- QUOTE.

/- TEXT:
我们证明 2 的平方根是无理数的核心
包含在以下定理中。
看看你能否使用 ``even_of_even_sqr`` 和定理 ``Nat.dvd_gcd``
来填充证明草稿。
BOTH: -/
-- QUOTE:
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
-- BOTH:
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    (mul_right_inj' (by norm_num)).mp this
-- BOTH:
  have : 2 ∣ n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [← this]
    apply dvd_mul_right
-- BOTH:
  have : 2 ∣ m.gcd n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_gcd <;>
    assumption
-- BOTH:
  have : 2 ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert this
    symm
    exact coprime_mn
-- BOTH:
  norm_num at this
-- QUOTE.

/- TEXT:
事实上，只需很少的改动，我们就可以将 ``2`` 替换为任意素数。
在下一个例子中试一试。
在证明的最后，你需要从 ``p ∣ 1``
推导出矛盾。
你可以使用 ``Nat.Prime.two_le``，它说
任何素数都大于或等于 2，
以及 ``Nat.le_of_dvd``。
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro sqr_eq
  have : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp this
    exact prime_p.ne_zero
  have : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right
  have : p ∣ Nat.gcd m n := by apply Nat.dvd_gcd <;> assumption
  have : p ∣ 1 := by
    convert this
    symm
    exact coprime_mn
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one this
  norm_num at this
-- QUOTE.

-- BOTH:
/- TEXT:
让我们考虑另一种方法。
这里是一个快速的证明：如果 :math:`p` 是素数，那么
:math:`m^2 \ne p n^2`：如果我们假设 :math:`m^2 = p n^2`
并考虑 :math:`m` 和 :math:`n` 的素因数分解，
那么 :math:`p` 在等式左边出现偶数次，
而在右边出现奇数次，矛盾。
注意这个论证要求 :math:`n` 和因此 :math:`m`
不等于零。
下面的形式化确认了这个假设是充分的。

唯一分解定理说任何非零的自然数
都可以以唯一的方式写成素数的乘积。
Mathlib 包含了这个定理的形式化版本，通过一个函数
``Nat.primeFactorsList`` 来表达，它返回一个数的
素因数列表，按非递减顺序排列。
该库证明了 ``Nat.primeFactorsList n`` 的所有元素
都是素数，任何大于零的 ``n`` 等于其
因数的乘积，
且如果 ``n`` 等于另一个素数列表的乘积，
那么该列表是 ``Nat.primeFactorsList n`` 的一个排列。
EXAMPLES: -/
-- QUOTE:
#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique
-- QUOTE.

/- TEXT:
你可以浏览这些定理和附近的其他定理，即使我们还没有
讨论列表成员关系、乘积或排列。
对于手头的任务，我们不需要这些。
相反，我们将利用 Mathlib 有函数 ``Nat.factorization`` 这一事实，
它将相同的数据表示为一个函数。
具体来说，``Nat.factorization n p``，我们也可以写作
``n.factorization p``，返回 ``p`` 在 ``n`` 的素因数分解中
的重数。我们将使用以下三个事实。
BOTH: -/
-- QUOTE:
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
-- QUOTE.

/- TEXT:
事实上，``n.factorization`` 在 Lean 中被定义为一个有限支撑的函数，
这解释了你逐步执行上面证明时会看到的奇怪记号。
现在不必担心这个。对于我们这里的目的，我们可以
将上述三个定理作为黑盒使用。

下一个例子表明化简器足够聪明，可以将
``n^2 ≠ 0`` 替换为 ``n ≠ 0``。策略 ``simpa`` 就是调用 ``simp``
然后调用 ``assumption``。

看看你能否使用上面的恒等式来填补证明中
缺失的部分。
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' prime_p.ne_zero nsqr_nez, prime_p.factorization', factorization_pow',
      add_comm]
-- BOTH:
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
-- QUOTE.

/- TEXT:
这个证明的一个好处是它也可以推广。这里
没有什么关于 ``2`` 的特殊之处；通过小改动，证明表明
每当我们写出 ``m^k = r * n^k`` 时，任何素数 ``p`` 在 ``r`` 中
的重数必须是 ``k`` 的倍数。

要用 ``r * n^k`` 使用 ``Nat.count_factors_mul_of_pos``，
我们需要知道 ``r`` 是正数。
但当 ``r`` 为零时，下面的定理是平凡的，并且
可以通过化简器轻松证明。
因此证明分情况进行。
行 ``rcases r with _ | r`` 将目标替换为两个版本：
一个将 ``r`` 替换为 ``0``，
另一个将 ``r`` 替换为 ``r + 1``。
在第二种情况下，我们可以使用定理 ``r.succ_ne_zero``，它
建立了 ``r + 1 ≠ 0``（``succ`` 代表后继）。

另请注意，以 ``have : npow_nz`` 开头的行提供了
``n^k ≠ 0`` 的简短证明项证明。
要理解它如何工作，尝试用策略证明替换它，
然后思考策略如何描述证明项。

看看你能否填补下面证明中缺失的部分。
在最后，你可以使用 ``Nat.dvd_sub'`` 和 ``Nat.dvd_mul_right``
来完成它。

注意这个例子不假设 ``p`` 是素数，但
当 ``p`` 不是素数时结论是平凡的，因为 ``r.factorization p``
根据定义为零，并且证明在所有情况下都有效。
BOTH: -/
-- QUOTE:
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (eq_zero_of_pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow', add_comm]
-- BOTH:
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_sub <;>
  apply Nat.dvd_mul_right
-- BOTH:
-- QUOTE.

/- TEXT:
我们可能希望通过多种方式改进这些结果。
首先，2 的平方根是无理数的证明
应该说一些关于 2 的平方根的内容，
它可以被理解为实数或复数的一个元素。
而说它是无理数应该说一些关于
有理数的内容，即没有有理数等于它。
此外，我们应该将本节中的定理推广到整数。
尽管数学上很明显，如果我们能将 2 的平方根
写成两个整数的商，那么我们就能将它写成
两个自然数的商，
但形式化地证明这一点需要一些努力。

在 Mathlib 中，自然数、整数、有理数、实数
和复数由不同的数据类型表示。
将注意力限制在不同的数域通常是有帮助的：
我们将看到在自然数上做归纳很容易，
而在不涉及实数的情况下推理整数的整除性
是最容易的。
但不得不在不同数域之间进行转换是一个令人头疼的问题，
我们必须面对它。
我们将在本章后面回到这个问题。

我们还应该期望能够加强最后一个定理的结论，
说数 ``r`` 是一个 ``k`` 次幂，
因为它的 ``k`` 次根就是每个整除 ``r`` 的素数
以其在 ``r`` 中的重数除以 ``k`` 的幂。
为了能这样做，我们需要更好的方法来推理
有限集上的乘积与和，
这也是我们将要回到的一个主题。

事实上，本节中的所有结果都在 Mathlib 中以
更一般的广泛性建立在 ``Data.Real.Irrational`` 中。
``multiplicity`` 的概念是为
任意交换幺半群定义的，
并且它取值于扩展的自然数 ``enat``，
它在自然数之上添加了无穷大的值。
在下一章中，我们将开始发展能够理解
Lean 如何支持这种一般性的手段。
EXAMPLES: -/
#check multiplicity

-- OMIT: TODO: add when available
-- #check irrational_nrt_of_n_not_dvd_multiplicity

-- #check irrational_sqrt_two

-- OMIT:
-- TODO: use this in the later section and then delete here.
#check Rat.num
#check Rat.den

section
variable (r : ℚ)

#check r.num
#check r.den
#check r.pos
#check r.reduced

end

-- example (r : ℚ) : r ^ 2 ≠ 2 := by
--   rw [← r.num_div_denom, div_pow]
--   have : (r.denom : ℚ) ^ 2 > 0 := by
--     norm_cast
--     apply pow_pos r.pos
--   have := Ne.symm (ne_of_lt this)
--   intro h
--   field_simp [this]  at h
--   norm_cast at h
--   sorry
