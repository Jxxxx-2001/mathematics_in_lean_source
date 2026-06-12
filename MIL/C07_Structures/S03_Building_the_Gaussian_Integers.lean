import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MIL.Common

/- TEXT:
.. _section_building_the_gaussian_integers:

构造高斯整数
------------------------------

我们现在将通过构造一个重要的数学对象——*高斯整数*，
来展示 Lean 中代数层级的使用，
并证明它是一个欧几里得整环。换句话说，根据我们一直使用的
术语，我们将定义高斯整数并证明它们是欧几里得整环结构的实例。

用通常的数学术语，高斯整数集合 :math:`\Bbb{Z}[i]`
是复数集合 :math:`\{ a + b i \mid a, b \in \Bbb{Z}\}`。
但我们不是将它们定义为复数的子集，
这里的目标是将它们本身定义为一个数据类型。我们通过
将高斯整数表示为一对整数（我们将它们视为
*实部*和*虚部*）来实现这一点。
BOTH: -/
-- QUOTE:
@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ
-- QUOTE.

/- TEXT:
我们首先证明高斯整数具有环的结构，
其中 ``0`` 定义为 ``⟨0, 0⟩``，``1`` 定义为 ``⟨1, 0⟩``，并且
加法逐点定义。要推导乘法的定义，
请记住我们希望元素 :math:`i`（由 ``⟨0, 1⟩`` 表示）是
:math:`-1` 的平方根。因此我们希望

.. math::

   (a + bi) (c + di) & = ac + bci + adi + bd i^2 \\
     & = (ac - bd) + (bc + ad)i.

这解释了下面 ``Mul`` 的定义。
BOTH: -/
namespace GaussInt

-- QUOTE:
instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
-- QUOTE.

/- TEXT:
正如 :numref:`section_structures` 中提到的，将与数据类型相关的所有
定义放在同名的命名空间中是个好主意。因此，在与本章相关联的 Lean
文件中，这些定义是在
``GaussInt`` 命名空间中进行的。

请注意，这里我们直接定义记号 ``0``、
``1``、``+``、``-`` 和 ``*`` 的解释，而不是将它们命名为
``GaussInt.zero`` 之类的名称再将记号分配给它。
为这些定义提供显式名称通常是有用的，例如，
用于 ``simp`` 和 ``rw``。
BOTH: -/
-- QUOTE:
theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl
-- QUOTE.

/- TEXT:
为计算实部和虚部的规则命名也很有用，
并将它们声明给简化器。
BOTH: -/
-- QUOTE:
@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl
-- QUOTE.

/- TEXT:
现在令人惊讶地容易证明高斯整数是一个交换环的实例。
我们正在充分利用结构体的概念。
每个特定的高斯整数是 ``GaussInt`` 结构体的一个实例，
而类型 ``GaussInt`` 本身，连同相关的运算，是
``CommRing`` 结构体的一个实例。而 ``CommRing`` 结构体又
扩展了记号结构体 ``Zero``、``One``、``Add``、
``Neg`` 和 ``Mul``。

如果你输入 ``instance : CommRing GaussInt := _``，点击 VS Code 中
出现的灯泡，然后要求 Lean 为该结构体定义填充一个骨架，
你会看到数量惊人的条目。
然而，跳转到该结构体的定义，可以看到许多
字段都有默认定义，Lean 会自动为你填写。
基本的条目出现在下面的定义中。
特殊情况是 ``nsmul`` 和 ``zsmul``，现在应该忽略它们，
下一章会解释。
在每种情况下，相关的恒等式
通过展开定义来证明，使用 ``ext`` 策略
将恒等式归结为其实部和虚部分量，
化简，并在必要时在整数中执行相关的环计算。
注意我们本可以轻松地避免重复所有这些代码，但
这不是当前讨论的主题。
BOTH: -/
-- QUOTE:
instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp
-- QUOTE.

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

/- TEXT:
Lean 的库将*非平凡*类型的类定义为至少有两个不同元素的类型。
在环的语境中，这等价于零不等于一。由于一些常见定理
依赖于该事实，我们不妨现在就建立它。
BOTH: -/
-- QUOTE:
instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp
-- QUOTE.

end GaussInt

/- TEXT:
我们现在将证明高斯整数具有一个重要的附加性质。
*欧几里得整环*是一个配备了*范数*
函数 :math:`N : R \to \mathbb{N}` 的环 :math:`R`，该函数具有以下两个性质：

- 对 :math:`R` 中任意的 :math:`a` 和 :math:`b \ne 0`，存在
  :math:`R` 中的 :math:`q` 和 :math:`r` 使得 :math:`a = bq + r` 且
  要么 :math:`r = 0` 要么 :math:`N(r) < N(b)`。
- 对任意的 :math:`a` 和 :math:`b \ne 0`，:math:`N(a) \le N(ab)`。

具有 :math:`N(a) = |a|` 的整数环 :math:`\Bbb{Z}` 是
欧几里得整环的一个原型例子。
在那种情况下，我们可以取 :math:`q` 为
:math:`a` 除以 :math:`b` 的整数除法结果，:math:`r`
为余数。这些函数在 Lean 中被定义为满足
以下条件：
EXAMPLES: -/
-- QUOTE:
example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.mul_ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt_abs a
-- QUOTE.

/- TEXT:
在任意环中，一个元素 :math:`a` 如果整除 :math:`1`，则被称为*单位*。
一个非零元素 :math:`a` 如果不能写成形式 :math:`a = bc`
（其中 :math:`b` 和 :math:`c` 都不是单位），则被称为*不可约的*。
在整数中，每个不可约元素 :math:`a` 都是*素元*，也就是说，每当 :math:`a`
整除一个乘积 :math:`bc` 时，它整除 :math:`b` 或 :math:`c`。但
在其他环中，这个性质可能会失效。在环
:math:`\Bbb{Z}[\sqrt{-5}]` 中，我们有

.. math::

  6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}),

且元素 :math:`2`、:math:`3`、:math:`1 + \sqrt{-5}` 和
:math:`1 - \sqrt{-5}` 都是不可约的，但它们不是素元。例如，
:math:`2` 整除乘积 :math:`(1 + \sqrt{-5})(1 - \sqrt{-5})`，
但它不整除任何一个因子。特别地，我们不再有
唯一分解：数字 :math:`6` 可以以不止一种方式分解为不可约元素。

相比之下，每个欧几里得整环都是唯一分解整环，这意味着
每个不可约元素都是素元。
欧几里得整环的公理意味着可以将任何非零元素
写为不可约元素的有限乘积。它们也意味着可以使用
欧几里得算法来找到任意两个非零元素 ``a`` 和 ``b`` 的最大公因数，
即能被任何其他公因数整除的元素。这反过来又意味着分解为
不可约元素在相差单位乘法的意义下是唯一的。

我们现在证明高斯整数是具有范数 :math:`N(a + bi) = (a + bi)(a - bi) = a^2 + b^2` 的
欧几里得整环。
高斯整数 :math:`a - bi` 被称为 :math:`a + bi` 的*共轭*。
不难验证对任意复数 :math:`x` 和 :math:`y`，
有 :math:`N(xy) = N(x)N(y)`。

要看出范数的这个定义使高斯整数成为一个欧几里得
整环，只有第一个性质具有挑战性。假设
我们想要为合适的 :math:`q` 和 :math:`r` 写出
:math:`a + bi = (c + di) q + r`。
将 :math:`a + bi` 和 :math:`c + di` 视为复数，进行除法

.. math::

  \frac{a + bi}{c + di} = \frac{(a + bi)(c - di)}{(c + di)(c-di)} =
    \frac{ac + bd}{c^2 + d^2} + \frac{bc -ad}{c^2+d^2} i.

实部和虚部可能不是整数，但我们可以将它们四舍五入到最近的
整数 :math:`u` 和 :math:`v`。然后我们可以将右边表示为
:math:`(u + vi) + (u' + v'i)`，其中 :math:`u' + v'i` 是剩余部分。
注意我们有 :math:`|u'| \le 1/2` 且 :math:`|v'| \le 1/2`，因此

.. math::

  N(u' + v' i) = (u')^2 + (v')^2 \le 1/4 + 1/4 \le 1/2.

两边乘以 :math:`c + di`，我们有

.. math::

  a + bi = (c + di) (u + vi) + (c + di) (u' + v'i).

令 :math:`q = u + vi` 和 :math:`r = (c + di) (u' + v'i)`，我们有
:math:`a + bi = (c + di) q + r`，并且我们只需要
界定 :math:`N(r)`：

.. math::

  N(r) = N(c + di)N(u' + v'i) \le N(c + di) \cdot 1/2 < N(c + di).

我们刚刚进行的论证需要将高斯整数视为复数的子集。
因此，在 Lean 中形式化它的一个选项是将高斯整数嵌入到复数中，
将整数嵌入到高斯整数中，定义从实数到整数的四舍五入函数，
并非常小心地在这些数系之间
适当地来回传递。
实际上，这正是 Mathlib 中遵循的方法，
其中高斯整数本身被构造为
*二次整数*环的一个特例。
参见文件 `GaussianInt.lean
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean>`_。

这里我们将改为进行一个保持在整数范围内的论证。
这展示了形式化数学时人们通常面临的一种选择。
给定一个需要库中没有的概念或工具的论证，
人们有两种选择：要么形式化所需的概念和工具，
要么调整论证以利用已有的概念和工具。
第一种选择在结果可以用于其他上下文时
通常是一个很好的时间投资。
但务实地说，有时寻找一个更初等的证明
更有效率。

整数的通常带余除法定理说对于
每个 :math:`a` 和非零的 :math:`b`，存在 :math:`q` 和 :math:`r`
使得 :math:`a = b q + r` 和 :math:`0 \le r < |b|`。
这里我们将利用以下变体，它说存在
:math:`q'` 和 :math:`r'` 使得
:math:`a = b q' + r'` 和 :math:`|r'| \le |b|/2`。
你可以检查，如果第一个陈述中的 :math:`r` 的值
满足 :math:`r \le |b|/2`，我们可以取 :math:`q' = q` 和 :math:`r' = r`，
否则我们可以取 :math:`q' = q + 1` 和 :math:`r' = r - b`
（对于 :math:`b` 为正的情况；否则做相应调整）。
我们感谢 Heather Macbeth 建议了以下更优雅的方法，
它避免了按情况定义。
我们只是在除法之前将 ``b / 2`` 加到 ``a`` 上，然后从余数中
减去它。
BOTH: -/
namespace Int

-- QUOTE:
def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.mul_ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.mul_ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  linarith
-- QUOTE.

/- TEXT:
注意我们老朋友 ``linarith`` 的使用。我们还需要将
``mod'`` 用 ``div'`` 来表示。
BOTH: -/
-- QUOTE:
theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]
-- QUOTE.

end Int

/- TEXT:
我们将使用事实 :math:`x^2 + y^2` 等于零当且仅当
:math:`x` 和 :math:`y` 都为零。作为练习，我们要求你证明
这在任何有序环中成立。
SOLUTIONS: -/
private theorem aux {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  haveI h' : x ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  eq_zero_of_pow_eq_zero h'

-- QUOTE:
-- BOTH:
theorem sq_add_sq_eq_zero {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num
-- QUOTE.

-- BOTH:
/- TEXT:
我们将本节中所有剩余的定义和定理
放在 ``GaussInt`` 命名空间中。
首先，我们定义 ``norm`` 函数并要求你建立
它的一些性质。
这些证明都很简短。
BOTH: -/
namespace GaussInt

-- QUOTE:
def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply add_nonneg <;>
  apply sq_nonneg

-- BOTH:
theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [norm, sq_add_sq_eq_zero, GaussInt.ext_iff]
  rfl

-- BOTH:
theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [lt_iff_le_and_ne, ne_comm, Ne, norm_eq_zero]
  simp [norm_nonneg]

-- BOTH:
theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [norm]
  ring

-- BOTH:
-- QUOTE.
/- TEXT:
接下来我们定义共轭函数：
BOTH: -/
-- QUOTE:
def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]
-- QUOTE.

/- TEXT:
最后，我们用记号 ``x / y`` 为高斯整数定义除法，
它将复商四舍五入到最近的高斯整数。
我们使用我们定制的 ``Int.div'`` 来实现这一目的。
正如我们上面计算的，如果 ``x`` 是 :math:`a + bi` 且 ``y`` 是 :math:`c + di`，
那么 ``x / y`` 的实部和虚部分别是最接近以下数值的
整数：

.. math::

  \frac{ac + bd}{c^2 + d^2} \quad \text{和} \quad \frac{bc -ad}{c^2+d^2},

这里分子是 :math:`(a + bi) (c - di)` 的实部和虚部，
分母都等于 :math:`c + di` 的范数。
BOTH: -/
-- QUOTE:
instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩
-- QUOTE.

/- TEXT:
定义了 ``x / y`` 之后，我们定义 ``x % y`` 为余数，
``x - (x / y) * y``。如上所述，我们将定义记录在
定理 ``div_def`` 和
``mod_def`` 中，以便我们可以用 ``simp`` 和 ``rw`` 使用它们。
BOTH: -/
-- QUOTE:
instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl
-- QUOTE.

/- TEXT:
这些定义立即对每个 ``x`` 和 ``y`` 产生
``x = y * (x / y) + x % y``，因此我们需要做的只是证明当 ``y`` 不为零时，
``x % y`` 的范数小于 ``y`` 的范数。

我们刚刚将 ``x / y`` 的实部和虚部分别定义为
``div' (x * conj y).re (norm y)`` 和 ``div' (x * conj y).im (norm y)``。
计算可得，我们有

  ``(x % y) * conj y = (x - x / y * y) * conj y = x * conj y - x / y * (y * conj y)``

右边表达式的实部和虚部正好是 ``mod' (x * conj y).re (norm y)`` 和 ``mod' (x * conj y).im (norm y)``。
根据 ``div'`` 和 ``mod'`` 的性质，
这些被保证小于或等于 ``norm y / 2``。
所以我们有

  ``norm ((x % y) * conj y) ≤ (norm y / 2)^2 + (norm y / 2)^2 ≤ (norm y / 2) * norm y``。

另一方面，我们有

  ``norm ((x % y) * conj y) = norm (x % y) * norm (conj y) = norm (x % y) * norm y``。

两边除以 ``norm y``，我们得到 ``norm (x % y) ≤ (norm y) / 2 < norm y``，
正如所需要的那样。

这个混乱的计算在下一个证明中完成。我们鼓励你
逐步检查细节，看看你能否找到更好的论证。
BOTH: -/
-- QUOTE:
theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith
-- QUOTE.

/- TEXT:
我们快要完成了。我们的 ``norm`` 函数将高斯整数映射到
非负整数。我们需要一个将高斯整数映射到自然数的函数，
我们通过将 ``norm`` 与函数
``Int.natAbs`` 组合来获得，后者将整数映射到自然数。
接下来两个引理中的第一个建立了将范数映射到自然数
再映射回整数不会改变其值。
第二个重新表达了范数递减的事实。
BOTH: -/
-- QUOTE:
theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  exact norm_mod_lt x hy
-- QUOTE.

/- TEXT:
我们还需要建立欧几里得整环上范数函数的
第二个关键性质。
BOTH: -/
-- QUOTE:
theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)
-- QUOTE.

/- TEXT:
我们现在可以将它们组合起来，证明高斯整数是
欧几里得整环的一个实例。我们使用我们定义的商和余数函数。
Mathlib 中欧几里得整环的定义比上面的更一般，
因为它允许我们证明余数相对于任何良基测度
递减。
比较一个返回自然数的范数的值是
这种测度的仅仅一个实例，
而在那种情况下，所需的性质就是定理
``natAbs_norm_mod_lt`` 和 ``not_norm_mul_left_lt_norm``。
BOTH: -/
-- QUOTE:
instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by rw [mod_def, add_comm] ; ring
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }
-- QUOTE.

/- TEXT:
一个直接的收获是，我们现在知道，在高斯整数中，
素元和不可约元的概念是一致的。
BOTH: -/
-- QUOTE:
example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime
-- QUOTE.

end GaussInt
