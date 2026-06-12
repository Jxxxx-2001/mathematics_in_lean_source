-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:
.. index:: vector subspace

子空间与商空间
-----------------------

子空间
^^^^^^^^^

正如线性映射是打包的，``V`` 的线性子空间也是一个打包结构，由
``V`` 中的一个集合（称为子空间的承载集）以及相关的封闭性质组成。
这里再次出现"模"这个词而不是向量空间，是因为 Mathlib
实际用于线性代数的更一般语境。
BOTH: -/
-- QUOTE:
section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx
end
-- QUOTE.

/- TEXT:
在上面的例子中，重要的是要理解 ``Submodule K V`` 是 ``V`` 的 ``K``-线性
子空间的类型，而不是一个谓词 ``IsSubmodule U``（其中 ``U`` 是 ``Set V`` 的元素）。
``Submodule K V`` 被赋予了到 ``Set V`` 的强制转换以及 ``V`` 上的成员谓词。
关于这样做的原因和方式，请参见 :numref:`section_hierarchies_subobjects`。

当然，两个子空间相同当且仅当它们具有相同的元素。这个事实
已注册供 ``ext`` 策略使用，该策略可以用于证明两个子空间相等，
就像它用于证明两个集合相等一样。

例如，要陈述并证明 ``ℝ`` 是 ``ℂ`` 的 ``ℝ``-线性子空间，
我们真正想要的是构造一个类型为 ``Submodule ℝ ℂ`` 的项，其到
``Set ℂ`` 的投影是 ``ℝ``，或者更精确地说，是 ``ℝ`` 在 ``ℂ`` 中的像。
EXAMPLES: -/
-- QUOTE:
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

-- QUOTE.

/- TEXT:
``Submodule`` 中证明字段末尾的撇号与 ``LinearMap`` 中的情况类似。
这些字段用 ``carrier`` 字段表述，因为它们是在
``MemberShip`` 实例之前定义的。然后它们被我们上面看到的 ``Submodule.add_mem``、``Submodule.zero_mem``
和 ``Submodule.smul_mem`` 所取代。

作为操作子空间和线性映射的练习，你将定义一个子空间在线性映射下的原像
（当然，我们下面会看到 Mathlib 已经知道这一点）。
记住，``Set.mem_preimage`` 可以用来重写涉及
成员关系和原像的陈述。除了上面讨论的关于 ``LinearMap`` 和 ``Submodule`` 的引理之外，
这是你唯一需要的引理。
BOTH: -/
-- QUOTE:
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [Set.mem_preimage, map_zero]
    exact H.zero_mem
-- BOTH:
  add_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rintro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply H.add_mem <;> assumption
-- BOTH:
  smul_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv
-- BOTH:
-- QUOTE.

/- TEXT:
利用类型类，Mathlib 知道向量空间的子空间继承了向量空间结构。
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K U := inferInstance
-- QUOTE.

/- TEXT:
这个例子很微妙。对象 ``U`` 不是一个类型，但 Lean 自动将其强制转换为
一个类型，将其解释为 ``V`` 的子类型。
因此，上面的例子可以更明确地重述为：
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance
-- QUOTE.

/- TEXT:

完备格结构与内直和
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

拥有类型 ``Submodule K V`` 而不是谓词
``IsSubmodule : Set V → Prop`` 的一个重要好处是，可以轻松地为 ``Submodule K V`` 赋予额外的结构。
重要的是，它在包含关系下具有完备格结构。
例如，我们使用格运算 ``⊓`` 来构造两个子空间的交，
而不是有一条引理陈述 ``V`` 的两个子空间的交仍然是子空间。
然后我们可以将关于格的任意引理应用于此构造。

让我们验证一下，两个子空间的下确界的基础集合确实是，
根据定义，它们的交集。
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl
-- QUOTE.

/- TEXT:
使用不同的记号来表示本质上就是基础集合的交集可能看起来有些奇怪，
但这种对应关系不能延续到上确界运算和集合并集，
因为子空间的并集通常不是一个子空间。
相反，需要使用由并集生成的子空间，这是通过
``Submodule.span`` 来完成的。
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]
-- QUOTE.

/- TEXT:
另一个微妙之处是 ``V`` 本身不具有类型 ``Submodule K V``，
因此我们需要一种方法将 ``V`` 视为 ``V`` 的子空间来讨论。
这也是由格结构提供的：整个子空间是这个格的顶元素。
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-- QUOTE.

/- TEXT:
类似地，这个格的底元素是其唯一元素为零元素的子空间。
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K
-- QUOTE.

/- TEXT:
特别是，我们可以讨论处于（内）直和的子空间的情况。
对于两个子空间的情况，我们使用通用谓词 ``IsCompl``，
它适用于任何有界偏序类型。
对于一般子空间族的情况，我们使用 ``DirectSum.IsInternal``。

EXAMPLES: -/
-- QUOTE:

-- 如果两个子空间处于直和中，则它们张成整个空间。
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- 如果两个子空间处于直和中，则它们仅在零处相交。
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- 如果子空间处于直和中，则它们张成整个空间。
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- 如果子空间处于直和中，则它们两两仅在零处相交。
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_iSupIndep.pairwiseDisjoint hij).eq_bot

-- 这些条件刻画了直和。
#check DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top

-- 与外直和的关系：如果一个子空间族处于
-- 内直和中，则从它们的外直和到 `V` 的映射
-- 是一个线性同构。
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end
-- QUOTE.

/- TEXT:

由集合张成的子空间
^^^^^^^^^^^^^^^^^^^^^^^^^

除了从已有子空间构造子空间之外，我们还可以使用
``Submodule.span K s`` 从任意集合 ``s`` 构造包含 ``s`` 的最小子空间。
在纸面上，通常使用这个空间由 ``s`` 中元素的所有线性组合构成这一事实。
但使用 ``Submodule.span_le`` 表达的泛性质和整个 Galois 连接理论
通常更高效。


EXAMPLES: -/
-- QUOTE:
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V
-- QUOTE.
/- TEXT:

当这些不够用时，可以使用相关的归纳原理
``Submodule.span_induction``，它确保只要一个性质对 ``zero`` 和 ``s`` 中的元素成立，
并且在加法和标量乘法下保持，那么该性质对 ``s`` 的生成的每个元素都成立。

作为练习，让我们重新证明 ``Submodule.mem_sup`` 的一个蕴含方向。
记住，你可以使用 `module` 策略来关闭由
``V`` 上各种代数运算的公理推出的目标。
BOTH: -/
-- QUOTE:

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
/- EXAMPLES:
  | mem y h =>
      sorry
  | zero =>
      sorry
  | add x y hx hy hx' hy' =>
      sorry
  | smul a x hx hx' =>
      sorry
SOLUTIONS: -/
  | mem x h =>
      rcases h with (hx|hx)
      · use x, hx, 0, T.zero_mem
        module
      · use 0, S.zero_mem, x, hx
        module
  | zero =>
      use 0, S.zero_mem, 0, T.zero_mem
      module
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      rcases hy' with ⟨s', hs', t', ht', rfl⟩
      use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
      module
  | smul a x hx hx' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
      module

-- QUOTE.
/- TEXT:

子空间的推与拉
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

正如之前承诺的，我们现在描述如何通过线性映射推送和拉回子空间。
像 Mathlib 中通常一样，第一个运算称为 ``map``，第二个称为
``comap``。
BOTH: -/
-- QUOTE:

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)
-- QUOTE.

/- TEXT:
注意，这些位于 ``Submodule`` 命名空间中，因此可以使用点记号写成
``E.map φ`` 而不是 ``Submodule.map φ E``，但这样读起来相当别扭（尽管有些
Mathlib 贡献者使用这种写法）。

特别是，线性映射的像和核都是子空间。这些特殊情况足够重要，
因而有专门的声明。
EXAMPLES: -/
-- QUOTE:
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- 或 `rfl`
-- QUOTE.


/- TEXT:
注意，我们不能写 ``φ.ker`` 来代替 ``LinearMap.ker φ``，因为 ``LinearMap.ker`` 也
适用于保持更多结构的映射类，因此它不期望参数
类型以 ``LinearMap`` 开头，所以点记号在这里不起作用。
然而，我们可以在右边使用另一种风格的点记号。因为
Lean 在 elaborating 左边之后期望一个类型为 ``Submodule K V`` 的项，它将
``.comap`` 解释为 ``Submodule.comap``。

以下引理给出了这些子模与 ``φ`` 的性质之间的关键关系。
BOTH: -/
-- QUOTE:

open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-- QUOTE.
/- TEXT:
作为练习，让我们证明 ``map`` 和 ``comap`` 的 Galois 连接性质。
可以使用以下引理，但这不是必需的，因为它们根据定义为真。
BOTH: -/
-- QUOTE:

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx
-- QUOTE.

/- TEXT:
商空间
^^^^^^^^^^^^^^^

商向量空间使用一般的商记号（输入 ``\quot``，而不是普通的
``/``）。
到商空间上的投影是 ``Submodule.mkQ``，泛性质是
``Submodule.liftQ``。
BOTH: -/
-- QUOTE:

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

-- QUOTE.
/- TEXT:
作为练习，让我们证明商空间子空间的对应定理。
Mathlib 知道一个稍微更精确的版本 ``Submodule.comapMkQRelIso``。
BOTH: -/
-- QUOTE:

open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
/- EXAMPLES:
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
SOLUTIONS: -/
  toFun F := ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
-- QUOTE.
