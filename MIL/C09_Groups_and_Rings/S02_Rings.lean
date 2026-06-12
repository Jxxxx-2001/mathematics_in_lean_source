-- BOTH:
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.QuotientRing
import MIL.Common

noncomputable section

/- TEXT:
.. _rings:

环
-----

.. index:: ring (algebraic structure)

环、其单位、态射和子环
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

类型 ``R`` 上的环结构的类型是 ``Ring R``。假设乘法交换的变体是 ``CommRing R``。我们已经看到 ``ring`` 策略将证明由交换环公理得出的任何等式。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
更奇特的变体不要求 ``R`` 上的加法构成群，而只要求是加法幺半群。相应的类型类是 ``Semiring R`` 和 ``CommSemiring R``。
自然数类型是 ``CommSemiring R`` 的一个重要实例，任何取值为自然数的函数类型也是如此。
另一个重要的例子是环中的理想类型，将在下面讨论。
``ring`` 策略的名称是双重误导的，因为它假设交换性，但也可以在半环中工作。换句话说，它适用于任何 ``CommSemiring``。
EXAMPLES: -/
-- QUOTE:
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
还有不假设乘法单位元存在或乘法结合律的环和半环类版本。我们在这里不讨论这些。

一些传统上在环论入门中教授的概念实际上是关于底层的乘法幺半群的。
一个突出的例子是环的单位（units）的定义。每个（乘法）幺半群 ``M`` 都有一个谓词 ``IsUnit : M → Prop``，断言存在双边逆元，一个单位类型 ``Units M``，记号为 ``Mˣ``，以及到 ``M`` 的强制转换。
类型 ``Units M`` 将可逆元素与其逆元以及确保每个确实是另一个的逆元的性质捆绑在一起。
这个实现细节主要在与定义可计算函数相关时才重要。在大多数情况下，可以使用 ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` 来构建一个单位。
在交换情况下，也有 ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ``，它将 ``x`` 构建为一个单位。
EXAMPLES: -/
-- QUOTE:
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance
-- QUOTE.

/- TEXT:
两个（半）环 ``R`` 和 ``S`` 之间的环同态类型是 ``RingHom R S``，记号为 ``R →+* S``。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f
-- QUOTE.

/- TEXT:
同构变体是 ``RingEquiv``，记号为 ``≃+*``。

与子幺半群和子群一样，有 ``Subring R`` 类型表示环 ``R`` 的子环，但这个类型远不如子群类型有用，因为不能商掉一个子环。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
-- QUOTE.

/- TEXT:
另请注意，``RingHom.range`` 产生一个子环。

理想与商
^^^^^^^^^^^^^^^^^^^^

由于历史原因，Mathlib 只有交换环的理想理论。
（环库最初是为了快速推进现代代数几何基础而开发的。）所以在本节中，我们将处理交换（半）环。
``R`` 的理想被定义为视为 ``R``-模的 ``R`` 的子模。模将在后面的线性代数章节中介绍，但这个实现细节大多可以安全地忽略，因为大多数（但不是全部）相关引理都会在理想的特殊上下文中重新陈述。但是匿名投影记号不会总是按预期工作。例如，在下面的代码片段中，不能用 ``I.Quotient.mk`` 替换 ``Ideal.Quotient.mk I``，因为有两个 ``.``，所以它会被解析为 ``(Ideal.Quotient I).mk``；但 ``Ideal.Quotient`` 本身并不存在。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem
-- QUOTE.

/- TEXT:
商环的泛性质是 ``Ideal.Quotient.lift``。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H
-- QUOTE.

/- TEXT:
特别地，它导致了环的第一同构定理。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- QUOTE.

/- TEXT:
理想在包含关系下形成一个完备格结构，同时也形成一个半环结构。这两个结构相互作用良好。
EXAMPLES: -/
section
-- QUOTE:
variable {R : Type*} [CommRing R] {I J : Ideal R}

-- EXAMPLES:
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf
-- QUOTE.

end

/- TEXT:
可以使用环同态通过 ``Ideal.map`` 和 ``Ideal.comap`` 分别前推和拉回理想。和通常一样，后者更方便使用，因为它不涉及存在量词。
这解释了为什么它被用来陈述允许我们在商环之间构建同态的条件。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H
-- QUOTE.

/- TEXT:
一个微妙之处是，类型 ``R ⧸ I`` 确实依赖于 ``I``
（直到定义相等），所以有一个证明两个理想 ``I`` 和 ``J`` 相等是不够的，不能使相应的商相等。然而，泛性质确实在这种情况下提供了一个同构。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h
-- QUOTE.

/- TEXT:
我们现在可以将中国剩余同构作为一个例子展示。注意区分索引下确界符号 ``⨅`` 和类型的大乘积符号 ``Π``。根据你的字体，它们可能很难区分。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf
-- QUOTE.

/- TEXT:
中国剩余定理的初等版本，一个关于 ``ZMod`` 的陈述，可以很容易地从上面的版本推导出来：
BOTH: -/
-- QUOTE:
open BigOperators PiNotation

-- EXAMPLES:
example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime
-- QUOTE.

/- TEXT:
作为一系列练习，我们将在一般情况下重证中国剩余定理。

我们首先需要使用商环的泛性质，将定理中出现的映射定义为一个环同态。
BOTH: -/
section
-- QUOTE:
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Pi.ringHom
#check ker_Pi_Quotient_mk

/-- 从 ``R ⧸ ⨅ i, I i`` 到 ``Π i, R ⧸ I i`` 的同态，出现于中国剩余定理中。 -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])
-- QUOTE.
-- BOTH:

/- TEXT:
确保接下来的两个引理可以通过 ``rfl`` 证明。
BOTH: -/
-- QUOTE:
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- BOTH:

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- QUOTE.
-- BOTH:

/- TEXT:
下一个引理证明了中国剩余定理中容易的一半，对理想族没有任何假设。证明不到一行。
EXAMPLES: -/
-- QUOTE:
#check injective_lift_iff

-- BOTH:
lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]
-- QUOTE.
-- BOTH:

/- TEXT:
我们现在准备好进入定理的核心，它将展示我们的 ``chineseMap`` 的满射性。首先我们需要知道表示互素性（也称为共极大性假设）的不同方式。下面只会用到前两种。
EXAMPLES: -/
-- QUOTE:
#check IsCoprime
#check isCoprime_iff_add
#check isCoprime_iff_exists
#check isCoprime_iff_sup_eq
#check isCoprime_iff_codisjoint
-- QUOTE.

/- TEXT:
我们借此机会在 ``Finset`` 上使用归纳法。关于 ``Finset`` 的相关引理在下面给出。
记住 ``ring`` 策略适用于半环，并且环的理想构成一个半环。
EXAMPLES: -/
-- QUOTE:
#check Finset.mem_insert_of_mem
#check Finset.mem_insert_self

-- BOTH:
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
/- EXAMPLES:
        1 = I + K                  := sorry
        _ = I + K * (I + J i)      := sorry
        _ = (1 + K) * I + K * J i  := sorry
        _ ≤ I + K ⊓ J i            := sorry
SOLUTIONS: -/
        1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf

-- QUOTE.

/- TEXT:
现在我们可以证明中国剩余定理中出现的映射的满射性。
BOTH: -/
-- QUOTE:
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      intros j hj
      exact hI _ _ (by simpa [ne_comm, isCoprime_iff_add] using hj)
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
-- BOTH:
  choose e he using key
  use mk _ (∑ i, f i * e i)
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext i
  rw [chineseMap_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]
-- QUOTE.
-- BOTH:

/- TEXT:
现在所有的部分都在下面组合在一起了：
BOTH: -/
-- QUOTE:
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }
-- QUOTE.

end

/- TEXT:
代数与多项式
^^^^^^^^^^^^^^^^^^^^^^^^

给定一个交换（半）环 ``R``，``R`` 上的*代数*是一个半环 ``A``，配备了一个环同态，其像与 ``A`` 中的每个元素交换。这被编码为类型类 ``Algebra R A``。
从 ``R`` 到 ``A`` 的同态称为结构映射，在 Lean 中记为 ``algebraMap R A : R →+* A``。
对于某个 ``r : R``，``a : A`` 乘以 ``algebraMap R A r`` 称为 ``a`` 被 ``r`` 的标量乘法，记为 ``r • a``。
注意，这种代数的概念有时称为*结合含幺代数*，以强调存在更一般的代数概念。

``algebraMap R A`` 是环同态这一事实打包了很多标量乘法的性质，例如下面的：
EXAMPLES: -/
-- QUOTE:
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a
-- QUOTE.

/- TEXT:
两个 ``R``-代数 ``A`` 和 ``B`` 之间的态射是与 ``R`` 中元素的标量乘法交换的环同态。它们是捆绑的态射，类型为 ``AlgHom R A B``，记为 ``A →ₐ[R] B``。

非交换代数的重要例子包括自同态代数和方阵代数，这两者都将在线性代数章节中介绍。
在本章中，我们将讨论交换代数最重要的例子之一，即多项式代数。

系数在 ``R`` 中的一元多项式代数称为 ``Polynomial R``，
一旦打开 ``Polynomial`` 命名空间，就可以写作 ``R[X]``。
从 ``R`` 到 ``R[X]`` 的代数结构映射记为 ``C``，
它代表"常数"（constant），因为相应的多项式函数总是常数。未定元记为 ``X``。
EXAMPLES: -/
section Polynomials
-- QUOTE:
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r
-- QUOTE.

/- TEXT:
在上面的第一个例子中，至关重要的是我们给 Lean 提供期望的类型，因为它不能从定义体中确定。在第二个例子中，目标多项式代数可以从我们对 ``C r`` 的使用中推断出来，因为 ``r`` 的类型是已知的。

因为 ``C`` 是从 ``R`` 到 ``R[X]`` 的环同态，我们可以使用所有的环同态引理，如 ``map_zero``、``map_one``、``map_mul`` 和 ``map_pow``，然后再在环 ``R[X]`` 中计算。例如：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring
-- QUOTE.

/- TEXT:
你可以使用 ``Polynomial.coeff`` 访问系数。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp
-- QUOTE.

/- TEXT:
定义多项式的次数总是很棘手，因为零多项式的特殊情况。Mathlib 有两个变体：``Polynomial.natDegree : R[X] → ℕ`` 将零多项式的次数赋予 ``0``，而 ``Polynomial.degree : R[X] → WithBot ℕ`` 赋予 ``⊥``。
在后者中，``WithBot ℕ`` 可以被视为 ``ℕ ∪ {-∞}``，除了 ``-∞`` 记为 ``⊥``，与完备格中的底元素是同一个符号。这个特殊值用作零多项式的次数，并且对加法是吸收的。（它对乘法几乎是吸收的，除了 ``⊥ * 0 = 0``。）

从道德上讲，``degree`` 版本是正确的。例如，它允许我们陈述乘积次数的期望公式（假设基环没有零因子）。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul
-- QUOTE.

/- TEXT:
而 ``natDegree`` 版本需要假设多项式非零。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq
-- QUOTE.

/- TEXT:
然而，``ℕ`` 比 ``WithBot ℕ`` 好用得多，所以 Mathlib 提供了两个版本，并提供了在它们之间转换的引理。此外，``natDegree`` 在计算复合次数时是更方便的定义。多项式的复合是 ``Polynomial.comp``，我们有：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp
-- QUOTE.

/- TEXT:
多项式产生多项式函数：任何多项式都可以使用 ``Polynomial.eval`` 在 ``R`` 上求值。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp
-- QUOTE.

/- TEXT:
特别地，有一个谓词 ``IsRoot``，对于使多项式为零的 ``R`` 中的元素 ``r`` 成立。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl
-- QUOTE.

/- TEXT:
我们想说，假设 ``R`` 没有零因子，一个多项式的根的个数不超过它的次数，其中根是按重数计算的。
但零多项式的情况再次令人痛苦。
所以 Mathlib 定义了 ``Polynomial.roots`` 将一个多项式 ``P`` 映到多重集（multiset），
即如果 ``P`` 是零多项式则定义为空，否则为 ``P`` 的根及其重数。这仅在底层环是整环时定义，
因为否则该定义没有良好的性质。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp
-- QUOTE.

/- TEXT:
``Polynomial.eval`` 和 ``Polynomial.roots`` 都只考虑系数环。它们不允许我们说 ``X ^ 2 - 2 : ℚ[X]`` 在 ``ℝ`` 中有根，或者 ``X ^ 2 + 1 : ℝ[X]`` 在 ``ℂ`` 中有根。为此，我们需要 ``Polynomial.aeval``，它将在任何 ``R``-代数中求 ``P : R[X]`` 的值。
更精确地说，给定一个半环 ``A`` 和一个 ``Algebra R A`` 实例，``Polynomial.aeval`` 将每个 ``a`` 的元素送到在 ``a`` 处求值的 ``R``-代数同态。由于 ``AlgHom`` 有到函数的强制转换，可以将其应用于一个多项式。但 ``aeval`` 不以多项式作为参数，所以不能像上面的 ``P.eval`` 那样使用点记号。
EXAMPLES: -/
-- QUOTE:
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

-- QUOTE.
/- TEXT:
在此上下文中对应于 ``roots`` 的函数是 ``aroots``，它接受一个多项式然后一个代数，并输出一个多重集（与 ``roots`` 相同，关于零多项式有相同的注意事项）。
EXAMPLES: -/
-- QUOTE:
open Complex Polynomial

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- Mathlib 知道 D'Alembert-Gauss 定理：``ℂ`` 是代数闭域。
example : IsAlgClosed ℂ := inferInstance

-- QUOTE.
/- TEXT:
更一般地，给定一个环同态 ``f : R →+* S``，可以使用 ``Polynomial.eval₂`` 在 ``S`` 中的一个点处求 ``P : R[X]`` 的值。这产生了一个从 ``R[X]`` 到 ``S`` 的实际函数，因为它不假设存在 ``Algebra R S`` 实例，所以点记号如你所预期的那样工作。
EXAMPLES: -/
-- QUOTE:
#check (Complex.ofRealHom : ℝ →+* ℂ)

example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofRealHom Complex.I = 0 := by simp
-- QUOTE.

/- TEXT:
最后让我们简要提一下多元多项式。给定一个交换半环 ``R``，系数在 ``R`` 中且未定元由类型 ``σ`` 索引的多项式的 ``R``-代数是 ``MVPolynomial σ R``。给定 ``i : σ``，相应的多项式是 ``MvPolynomial.X i``。（和往常一样，可以打开 ``MVPolynomial`` 命名空间将其缩短为 ``X i``。）
例如，如果我们想要两个未定元，可以使用 ``Fin 2`` 作为 ``σ``，并将定义 :math:`\mathbb{R}^2` 中单位圆的多项式写为：
EXAMPLES: -/
-- QUOTE:
open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1
-- QUOTE.

/- TEXT:
回忆一下，函数应用具有非常高的优先级，所以上面的表达式读作 ``(X 0) ^ 2 + (X 1) ^ 2 - 1``。
我们可以求值以确保坐标为 :math:`(1, 0)` 的点在圆上。
回忆 ``![...]`` 记号表示对于某个由参数数量确定的自然数 ``n`` 和由参数类型确定的某个类型 ``X``，``Fin n → X`` 的元素。
EXAMPLES: -/
-- QUOTE:
example : MvPolynomial.eval ![1, 0] circleEquation = 0 := by simp [circleEquation]
-- QUOTE.

end Polynomials
