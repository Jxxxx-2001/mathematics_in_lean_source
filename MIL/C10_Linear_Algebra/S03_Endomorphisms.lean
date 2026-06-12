-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


/- TEXT:

自同态
--------------

线性映射的一个重要特例是自同态：从向量空间到自身的线性映射。
它们之所以有趣，是因为它们构成一个 ``K``-代数。特别地，我们可以对其求值系数在 ``K`` 中的多项式，
并且它们可以有特征值和特征向量。

Mathlib 使用缩写 ``Module.End K V := V →ₗ[K] V``，这在
大量使用它们时很方便（尤其是在打开 ``Module`` 命名空间之后）。

BOTH: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap End

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ -- `rfl` 也可以

-- 在 `φ` 上求值 `P`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- 在 `φ` 上求值 `X` 将返回 `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ


-- QUOTE.
/- TEXT:
作为操作自同态、子空间和多项式的练习，让我们证明
（二元）核引理：对任意自同态 :math:`φ` 和任意两个互素
多项式 :math:`P` 和 :math:`Q`，我们有 :math:`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)`。

注意，``IsCoprime x y`` 定义为 ``∃ a b, a * x + b * y = 1``。
BOTH: -/
-- QUOTE:

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simpa [hx]
-- BOTH:

#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- 或者下面的替代方法：
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- 或者与上面一样的替代方法
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]

-- QUOTE.
/- TEXT:
现在我们转向特征空间和特征值的讨论。与自同态 :math:`φ` 和标量 :math:`a` 关联的特征空间
是 :math:`φ - aId` 的核。
特征空间对所有的 ``a`` 值都有定义，尽管
它们只在非零时才有意义。
然而，特征向量根据定义是特征空间中的非零元素。相应的
谓词是 ``End.HasEigenvector``。
EXAMPLES: -/
-- QUOTE:
example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def


-- QUOTE.
/- TEXT:
还有一个谓词 ``End.HasEigenvalue`` 和相应的子类型 ``End.Eigenvalues``。
EXAMPLES: -/
-- QUOTE:

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- 特征值是极小多项式的根
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- 在有限维情况下，逆命题也成立（我们将在下面讨论维数）
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton 定理
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly

-- QUOTE.
