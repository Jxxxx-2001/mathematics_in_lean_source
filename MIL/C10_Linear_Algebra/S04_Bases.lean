-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

import MIL.Common

/- TEXT:

.. _matrices_bases_dimension:

矩阵、基与维数
-----------------------------

.. _matrices:

矩阵
^^^^^^^^

.. index:: matrices

在引入抽象向量空间的基之前，我们先回到更初等的背景：
某域 :math:`K` 上 :math:`K^n` 中的线性代数。
这里的主要对象是向量和矩阵。
对于具体向量，可以使用 ``![…]`` 记号，其中分量用逗号分隔。
对于具体矩阵，我们可以使用 ``!![…]`` 记号，行用分号分隔，
行内的分量用逗号分隔。
当元素具有可计算类型（如 ``ℕ`` 或 ``ℚ``）时，我们可以使用
``eval`` 命令来试验基本运算。

EXAMPLES: -/
-- QUOTE:

section matrices

-- 向量加法
#eval ![1, 2] + ![3, 4]  -- ![4, 6]

-- 矩阵加法
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- 矩阵乘法
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]

-- QUOTE.
/- TEXT:
重要的是要理解，这种 ``#eval`` 的使用仅对探索
有意义，它并不意在取代像 Sage 这样的计算机代数系统。
这里用于矩阵的数据表示在计算上
*不* 是高效的。它使用函数而非数组，优化的是
证明而非计算。
``#eval`` 使用的虚拟机也并非为此用途优化。


注意，矩阵记号列出的是行，但向量记号
既不是行向量也不是列向量。矩阵左乘（或右乘）向量
将向量解释为行（或列）向量。
这对应于运算
``Matrix.vecMul``（记号为 ``ᵥ*``）和 ``Matrix.mulVec``（记号为 ``*ᵥ``）。
这些记号的作用域在 ``Matrix`` 命名空间中，因此我们需要打开它。
EXAMPLES: -/
-- QUOTE:
open Matrix

-- 矩阵左乘向量
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- 矩阵左乘向量，结果是一个一行的矩阵
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- 矩阵右乘向量
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]
-- QUOTE.
/- TEXT:
要生成由向量指定的相同行或列的矩阵，我们
使用 ``Matrix.replicateRow`` 和 ``Matrix.replicateCol``，其参数是索引行
或列的类型以及向量。
例如，可以得到单行或单列矩阵（更准确地说，其行
或列由 ``Fin 1`` 索引的矩阵）。
EXAMPLES: -/
-- QUOTE:
#eval replicateRow (Fin 1) ![1, 2] -- !![1, 2]

#eval replicateCol (Fin 1) ![1, 2] -- !![1; 2]
-- QUOTE.
/- TEXT:
其他熟悉的操作包括向量点积、矩阵转置，以及
对于方阵，行列式和迹。
EXAMPLES: -/
-- QUOTE:

-- 向量点积
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- 矩阵转置
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- 行列式
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- 迹
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`


-- QUOTE.
/- TEXT:
当元素不具有可计算类型时，例如如果它们是实数，我们不能
期望 ``#eval`` 能够提供帮助。而且这种求值不能在证明中使用，
因为这会使可信代码库（即在检查证明时需要信任的 Lean 部分）膨胀得很大。

因此，在证明中使用 ``simp`` 和 ``norm_num`` 策略，或
它们在命令中的对应版本来快速探索，也是很好的做法。
EXAMPLES: -/
-- QUOTE:

#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

-- QUOTE.
/- TEXT:
方阵的下一个重要运算是求逆。
与数的除法总是有定义并在除以零时返回人为规定的值零一样，
求逆运算对所有矩阵都有定义，并对不可逆矩阵返回
零矩阵。

更准确地说，有一个通用函数 ``Ring.inverse``，它在任何环中都这样做，
并且，对于任何矩阵 ``A``，``A⁻¹`` 被定义为 ``Ring.inverse A.det • A.adjugate``。
根据 Cramer 法则，当 ``A`` 的行列式不为零时，这确实是 ``A`` 的逆。
EXAMPLES: -/
-- QUOTE:

#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

-- QUOTE.
/- TEXT:
当然，这个定义仅对可逆矩阵真正有用。
有一个通用类型类 ``Invertible`` 可以帮助记录这一点。
例如，下例中的 ``simp`` 调用将使用 ``inv_mul_of_invertible``
引理，该引理具有 ``Invertible`` 类型类假设，因此只有在
类型类综合系统能够找到它时才会触发。
这里我们使用 ``have`` 语句使这一事实可用。
EXAMPLES: -/
-- QUOTE:

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

-- QUOTE.
/- TEXT:
在这个完全具体的情况下，我们也可以使用 ``norm_num`` 机制，
并用 ``apply?`` 找到最后一行：
EXAMPLES: -/
-- QUOTE:
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

-- QUOTE.
/- TEXT:
上面所有的具体矩阵的行和列都由某个 ``n`` 的 ``Fin n`` 索引
（行和列的 ``n`` 不一定相同）。
但有时使用任意有限类型来索引矩阵更为方便。
例如，有限图的邻接矩阵的行和列自然地由
图的顶点索引。

事实上，当仅仅想定义矩阵而不在其上定义任何运算时，
索引类型的有限性甚至不是必需的，且系数可以具有任何类型，
无需任何代数结构。
因此 Mathlib 简单地将 ``Matrix m n α`` 定义为 ``m → n → α``（对于任意类型 ``m``、``n`` 和 ``α``），
而我们迄今一直使用的矩阵具有诸如 ``Matrix (Fin 2) (Fin 2) ℝ`` 这样的类型。
当然，代数运算要求对 ``m``、``n`` 和 ``α`` 有更多假设。

注意，我们不直接使用 ``m → n → α`` 的主要原因是，这能让类型类
系统理解我们想要什么。例如，对于环 ``R``，类型 ``n → R`` 被赋予
逐点乘法运算，类似地，``m → n → R``
也具有这种运算，但这并*不*是我们想要的矩阵乘法。

在下面的第一个例子中，我们强制 Lean 看穿 ``Matrix`` 的定义
并接受该陈述是有意义的，然后通过检查所有元素来证明它。

但接下来的两个例子表明，Lean 对 ``Fin 2 → Fin 2 → ℤ`` 使用逐点乘法，
但对 ``Matrix (Fin 2) (Fin 2) ℤ`` 使用矩阵乘法。
EXAMPLES: -/
-- QUOTE:
section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num
-- QUOTE.
/- TEXT:
要将矩阵定义为函数同时不失 ``Matrix`` 对
类型类综合的优势，我们可以使用函数与矩阵之间的等价 ``Matrix.of``。
这个等价在内部是使用 ``Equiv.refl`` 定义的。

例如，我们可以定义对应于向量 ``v`` 的 Vandermonde 矩阵。
EXAMPLES: -/
-- QUOTE:

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl
end
end matrices
-- QUOTE.
/- TEXT:
基
^^^^^

我们现在要讨论向量空间的基。非正式地说，有许多方式来定义这个概念。
可以使用泛性质。
可以说基是一族线性无关且张成整个空间的向量。
或者可以将这些性质结合起来，直接说基是一族向量，
使得每个向量都可以唯一地写成基向量的线性组合。
另一种说法是，基提供了与基域 ``K``（视为 ``K`` 上的向量空间）的幂之间的线性同构。

这个同构版本实际上是 Mathlib 在底层使用的定义，
其他刻画都是从中证明出来的。
在无穷基的情况下，对"``K`` 的幂"这一想法需要稍加小心。
事实上，在这个代数语境中只有有限线性组合是有意义的。因此我们需要的
参考向量空间不是 ``K`` 的拷贝的直积，而是直和。
我们可以对某个索引基的指标类型 ``ι`` 使用 ``⨁ i : ι, K``。
但我们更倾向于使用更专门化的写法 ``ι →₀ K``，它表示
"从 ``ι`` 到 ``K`` 的具有有限支集的函数"，即除了 ``ι`` 中的一个有限集外为零的函数
（这个有限集不是固定的，它取决于函数）。
对来自基 ``B`` 的这样一个函数在向量 ``v`` 和
``i : ι`` 处求值，返回 ``v`` 在第 ``i`` 个基向量上的分量（或坐标）。

由类型 ``ι`` 索引的 ``V`` 作为 ``K`` 向量空间的基的类型是 ``Basis ι K V``。
该同构被称为 ``Basis.repr``。
BOTH: -/
-- QUOTE:
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

open Module

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- 索引为 ``i`` 的基向量
#check (B i : V)

-- 由 ``B`` 给出的与模型空间的线性同构
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- ``v`` 的分量函数
#check (B.repr v : ι →₀ K)

-- ``v`` 在索引 ``i`` 处的分量
#check (B.repr v i : K)

-- QUOTE.
/- TEXT:
除了从这样的同构出发，也可以从一族线性无关且张成整个空间的向量 ``b`` 出发，
这就是 ``Basis.mk``。

该族向量张成整个空间的假设写作 ``⊤ ≤ Submodule.span K (Set.range b)``。
这里 ``⊤`` 是 ``V`` 的顶子模，即 ``V`` 视为自身的子模。
这种写法看起来有些绕，但我们下面会看到，它根据定义几乎等价于
更易读的 ``∀ v, v ∈ Submodule.span K (Set.range b)``
（下面代码片段中的下划线指的是无用的信息 ``v ∈ ⊤``）。
EXAMPLES: -/
-- QUOTE:
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- 上述基的基础向量族确实是 ``b``。
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

-- QUOTE.
/- TEXT:
特别地，模型向量空间 ``ι →₀ K`` 有一个所谓的标准基，其 ``repr``
函数在任意向量上求值都是恒等同构。它被称为
``Finsupp.basisSingleOne``，其中 ``Finsupp`` 表示具有有限支集的函数，
``basisSingleOne`` 指的是基向量是在单个输入值处
非零的函数。更准确地说，由 ``i : ι`` 索引的基向量
是 ``Finsupp.single i 1``，即是在 ``i`` 处取值为 ``1``
且其他地方为 ``0`` 的有限支集函数。

BOTH: -/
-- QUOTE:
variable [DecidableEq ι]
-- QUOTE.

-- EXAMPLES:
-- QUOTE:
example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- QUOTE.
/- TEXT:
当索引类型有限时，不需要有限支集函数的故事。
在这种情况下，我们可以使用更简单的 ``Pi.basisFun``，它给出整个
``ι → K`` 的基。
EXAMPLES: -/
-- QUOTE:

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- QUOTE.
/- TEXT:
回到抽象向量空间基的一般情况，我们可以将
任意向量表示为基向量的线性组合。
让我们先看看有限基的简单情况。
EXAMPLES: -/
-- QUOTE:

example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v


-- QUOTE.

/- TEXT:
当 ``ι`` 不是有限时，上述陈述先验地没有意义：我们不能对 ``ι`` 求和。
然而，被求和函数的支集是有限的（它是 ``B.repr v`` 的支集）。
但我们需要应用一个考虑到这一点的构造。
这里 Mathlib 使用了一个特设的函数，需要一些时间来适应：
``Finsupp.linearCombination``（它建立在更一般的 ``Finsupp.sum`` 之上）。
给定从类型 ``ι`` 到基域 ``K`` 的有限支集函数 ``c`` 以及任意
从 ``ι`` 到 ``V`` 的函数 ``f``，``Finsupp.linearCombination K f c`` 是
在 ``c`` 的支集上对标量乘法 ``c • f`` 的求和。特别地，
我们可以用包含 ``c`` 的支集的任意有限集上的求和来代替它。

EXAMPLES: -/
-- QUOTE:

example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h
-- QUOTE.
/- TEXT:
也可以假设 ``f`` 是有限支集的，仍然得到良好定义的求和。
但 ``Finsupp.linearCombination`` 所做的选择与我们关于基的讨论相关，因为它允许
陈述 ``Basis.sum_repr`` 的推广。
EXAMPLES: -/
-- QUOTE:

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
-- QUOTE.
/- TEXT:
人们可能会好奇为什么 ``K`` 在这里是显式参数，尽管它可以从
``c`` 的类型推断出来。关键在于部分应用的 ``Finsupp.linearCombination K f``
本身是有趣的。它不是一个从 ``ι →₀ K`` 到 ``V`` 的裸函数，而是一个
``K``-线性映射。
EXAMPLES: -/
-- QUOTE:
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)

-- QUOTE.
/- TEXT:
回到数学讨论，重要的是要理解，在形式化
数学中，向量在基中的表示可能不如你想象的那么有用。
事实上，直接使用基的更抽象的性质往往高效得多。
特别地，基的泛性质将它们与代数中的其他自由对象联系起来，
允许通过指定基向量的像来构造线性映射。
这就是 ``Basis.constr``。对于任何 ``K``-向量空间 ``W``，我们的基 ``B``
给出一个线性同构 ``Basis.constr B K``，从 ``ι → W`` 到 ``V →ₗ[K] W``。
这个同构的特征在于它将任意函数 ``u : ι → W``
发送到一个线性映射，该线性映射将基向量 ``B i`` 发送到 ``u i``，对于每个 ``i : ι``。
BOTH: -/
-- QUOTE:
section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

-- QUOTE.
/- TEXT:
这个性质确实是刻画性的，因为线性映射由它们在基上的取值决定：
EXAMPLES: -/
-- QUOTE:
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h


-- QUOTE.
/- TEXT:
如果我们在目标空间上也有一个基 ``B'``，那么我们可以将线性映射
与矩阵等同起来。这个等同是一个 ``K``-线性同构。
BOTH: -/
-- QUOTE:


variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- 获取矩阵与向量之间乘法的 ``*ᵥ`` 记号。

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end

-- QUOTE.
/- TEXT:
作为这个主题的练习，我们将证明保证自同态具有良好定义的行列式的定理的一部分。
也就是说，我们要证明当两个基由同一类型索引时，它们
附加到任何自同态的矩阵具有相同的行列式。
这之后还需要补充证明基都具有同构的索引类型才能得到
完整的结果。

当然 Mathlib 已经知道这一点，``simp`` 可以立即关闭目标，所以你不应该过早使用它，
而应该使用提供的引理。
BOTH: -/
-- QUOTE:

open Module LinearMap Matrix

-- 一些来自 `LinearMap.toMatrix` 是代数态射这一事实的引理。
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- 一些来自 ``Matrix.det`` 是乘法幺半群态射这一事实的引理。
#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have F : M = P' * M' * P := by
    rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  have F' : P' * P = 1 := by
    rw [← toMatrix_comp, id_comp, toMatrix_id]
  rw [F, Matrix.det_mul, Matrix.det_mul,
      show P'.det * M'.det * P.det = P'.det * P.det * M'.det by ring, ← Matrix.det_mul, F',
      Matrix.det_one, one_mul]
-- BOTH:
end

-- QUOTE.
/- TEXT:

维数
^^^^^^^^^

回到单个向量空间的情况，基对于定义维数概念也很有用。
这里同样有有限维向量空间的基本情况。
对于这样的空间，我们期望维数是一个自然数。
这就是 ``Module.finrank``。它以基域作为显式参数，
因为给定的交换群可以是不同域上的向量空间。

EXAMPLES: -/
-- QUOTE:
section

#check (Module.finrank K V : ℕ)

-- `Fin n → K` 是 `K` 上维数为 `n` 的原型空间。
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- 视为自身上的向量空间，`ℂ` 的维数为一。
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- 但作为实向量空间，它的维数为二。
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- QUOTE.
/- TEXT:
注意，``Module.finrank`` 对任何向量空间都有定义。对于无穷维向量空间，
它返回零，就像除以零返回零一样。

当然，许多引理需要有限维假设。这就是
``FiniteDimensional`` 类型类的作用。例如，思考一下如果没有这个假设，
下一个例子为什么会失败。
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff

-- QUOTE.
/- TEXT:
在上述陈述中，``Nontrivial V`` 表示 ``V`` 至少有两个不同的元素。
注意，``Module.finrank_pos_iff`` 没有显式参数。
当从左到右使用时这没问题，但当从右到左使用时就不行，
因为 Lean 无法从 ``Nontrivial V`` 这个陈述中猜测出 ``K``。
在这种情况下，使用名称参数语法是很有用的，在检查引理
是在名为 ``R`` 的环上陈述的之后。所以我们可以写：
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

-- QUOTE.
/- TEXT:
上面的写法有些奇怪，因为我们已经有了 ``h`` 作为假设，所以我们
完全可以给出完整的证明 ``Module.finrank_pos_iff.1 h``，但对于
更复杂的情况，了解这种方法是有好处的。

根据定义，``FiniteDimensional K V`` 可以从任意基读取。
EXAMPLES: -/
-- QUOTE:
variable {ι : Type*} (B : Module.Basis ι K V)

example [Finite ι] : FiniteDimensional K V := Module.Basis.finiteDimensional_of_finite B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
-- QUOTE.
/- TEXT:
利用线性子空间对应的子类型具有向量空间结构这一事实，
我们可以讨论子空间的维数。
BOTH: -/
-- QUOTE:

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E
-- QUOTE.
/- TEXT:
在上面第一个陈述中，类型归属的目的是确保
到 ``Type*`` 的强制转换不会过早触发。

现在我们准备好了一个关于 ``finrank`` 和子空间的练习。
BOTH: -/
-- QUOTE:
example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← finrank_pos_iff (R := K)]
  have := Submodule.finrank_sup_add_finrank_inf_eq E F
  have := Submodule.finrank_le E
  have := Submodule.finrank_le F
  have := Submodule.finrank_le (E ⊔ F)
  linarith
-- BOTH:
end
-- QUOTE.

/- TEXT:
现在让我们转向维数理论的一般情况。在这种情况下
``finrank`` 没有用，但我们仍然有以下事实：对于同一个
向量空间的任意两个基，索引这些基的类型之间存在双射。因此我们
仍然可以希望将秩定义为基数，即"类型的集合在存在双射等价
关系下的商"的一个元素。

在讨论基数时，像我们在本书其他地方那样忽略围绕 Russell 悖论的基础问题
变得更加困难。
不存在所有类型的类型，因为这会导致逻辑不一致性。
这个问题由我们通常试图忽略的宇宙层级
来解决。

每个类型都有一个宇宙层级，这些层级的行为类似于自然
数。特别地，存在第零层，对应的宇宙
``Type 0`` 简单地记为 ``Type``。这个宇宙足以容纳
几乎所有经典数学。例如 ``ℕ`` 和 ``ℝ`` 具有类型 ``Type``。
每个层级 ``u`` 有一个后继，记为
``u + 1``，且 ``Type u`` 具有类型 ``Type (u+1)``。

但宇宙层级不是自然数，它们具有真正不同的性质，并且
没有一个类型。特别地，你不能在 Lean 中陈述类似 ``u ≠ u + 1`` 的东西。
根本没有可以容纳这个陈述的类型。甚至陈述
``Type u ≠ Type (u+1)`` 也没有任何意义，因为 ``Type u`` 和 ``Type (u+1)``
具有不同的类型。

每当我们写 ``Type*`` 时，Lean 会插入一个名为 ``u_n`` 的宇宙层级变量，其中 ``n`` 是一个
数字。这允许定义和陈述存在于所有宇宙中。

给定一个宇宙层级 ``u``，我们可以在 ``Type u`` 上定义一个等价关系，说
两个类型 ``α`` 和 ``β`` 是等价的，如果它们之间存在双射。
商类型 ``Cardinal.{u}`` 位于 ``Type (u+1)`` 中。花括号
表示宇宙变量。``α : Type u`` 在这个商中的像是
``Cardinal.mk α : Cardinal.{u}``。

但我们不能直接比较不同宇宙中的基数。因此，从技术上讲，我们
不能将向量空间 ``V`` 的秩定义为索引
``V`` 的基的所有类型的基数。
因此，它被定义为 ``V`` 中所有线性无关集的基数
的上确界 ``Module.rank K V``。如果 ``V`` 具有宇宙层级 ``u``，那么
它的秩具有类型 ``Cardinal.{u}``。


EXAMPLES: -/
-- QUOTE:
#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}

-- QUOTE.
/- TEXT:
仍然可以将这个定义与基联系起来。事实上，宇宙层级上还有一个交换的 ``max``
运算，给定两个宇宙层级 ``u`` 和 ``v``，
存在一个运算 ``Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}``，
它允许将基数放入共同的宇宙中并陈述维数定理。
EXAMPLES: -/
-- QUOTE:

universe u v -- `u` 和 `v` 将表示宇宙层级

variable {ι : Type u} (B : Module.Basis ι K V)
         {ι' : Type v} (B' : Module.Basis ι' K V)

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
-- QUOTE.
/- TEXT:
我们可以通过从自然数到有限基数（或更准确地说，位于 ``Cardinal.{v}`` 中的有限基数，其中 ``v`` 是 ``V`` 的宇宙层级）的强制转换，
将有限维情况与这个讨论联系起来。
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
-- QUOTE.
