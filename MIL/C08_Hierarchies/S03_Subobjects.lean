import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_subobjects:

子对象
-----------

在定义了某种代数结构及其态射之后，下一步是考虑继承此代数结构的集合，例如子群或子环。
这与我们之前的话题有很大重叠。事实上，``X`` 中的一个集合被实现为从 ``X`` 到 ``Prop`` 的函数，因此子对象是满足某个谓词的函数。
因此我们可以重用许多导致 ``DFunLike`` 类及其后代的思想。我们不会重用 ``DFunLike`` 本身，因为这会破坏从 ``Set X`` 到 ``X → Prop`` 的抽象屏障。取而代之的是有一个 ``SetLike`` 类。这个类不是将一个单射包装成函数类型，而是将单射包装成 ``Set`` 类型，并定义相应的强制转换和 ``Membership`` 实例。

BOTH: -/

-- QUOTE:
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- 子幺半群的承载集. -/
  carrier : Set M
  /-- 子幺半群中两个元素的乘积仍属于该子幺半群. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- 单位元属于该子幺半群. -/
  one_mem : 1 ∈ carrier

/-- `M` 中的子幺半群可以被视为 `M` 中的集合。 -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

-- QUOTE.

/- TEXT:
配备了上述 ``SetLike`` 实例，我们已经可以自然地陈述子幺半群 ``N`` 包含 ``1`` 而不使用 ``N.carrier``。
我们也可以默默地将 ``N`` 视为 ``M`` 中的集合，并在映射下取其直接像。
BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N
-- QUOTE.

/- TEXT:
我们还有到 ``Type`` 的强制转换，它使用 ``Subtype``，因此给定一个子幺半群 ``N``，我们可以写一个参数 ``(x : N)``，它可以被强制转换为属于 ``N`` 的 ``M`` 的元素。

BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property
-- QUOTE.

/- TEXT:
使用这个到 ``Type`` 的强制转换，我们也可以处理为子幺半群配备幺半群结构的任务。我们将使用从关联于 ``N`` 的类型到 ``M`` 的强制转换，以及断言此强制转换是单射的引理 ``SetCoe.ext``。这两者都由 ``SetLike`` 实例提供。

BOTH: -/

-- QUOTE:
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))
-- QUOTE.

/- TEXT:
注意，在上面的实例中，我们可以不使用到 ``M`` 的强制转换和调用 ``property`` 字段，而是使用解构绑定，如下所示。

BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
-- QUOTE.

/- TEXT:

为了将关于子幺半群的引理应用于子群或子环，我们需要一个类，就像态射一样。注意，这个类接受一个 ``SetLike`` 实例作为参数，因此它不需要承载集字段，并可以在其字段中使用成员关系记号。
BOTH: -/

-- QUOTE:
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem
-- QUOTE.

/- TEXT:

作为练习，你应该定义一个 ``Subgroup₁`` 结构体，赋予它一个 ``SetLike`` 实例和一个 ``SubmonoidClass₁`` 实例，在关联于 ``Subgroup₁`` 的子类型上放置一个 ``Group`` 实例，并定义一个 ``SubgroupClass₁`` 类。

SOLUTIONS: -/
@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  /-- 子群中元素的逆元仍属于该子群. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier


/-- `M` 中的子群可以被视为 `M` 中的集合。 -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun H ↦ H.toSubmonoid₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

instance [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul_cancel := fun x ↦ SetCoe.ext (inv_mul_cancel (x : G)) }

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] : Prop
    extends SubmonoidClass₁ S G where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun H ↦ H.toSubmonoid₁.mul_mem
  one_mem := fun H ↦ H.toSubmonoid₁.one_mem

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G :=
{ (inferInstance : SubmonoidClass₁ (Subgroup₁ G) G) with
  inv_mem := Subgroup₁.inv_mem }

/- TEXT:
关于 Mathlib 中给定代数对象的子对象，另一件非常重要的事情是，它们总是形成一个完备格，并且这个结构被大量使用。例如，你可能会寻找一个引理，说明子幺半群的交集是子幺半群。但这不会是一个引理，这将是一个下确界构造。让我们考虑两个子幺半群的情况。

BOTH: -/

-- QUOTE:
instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
-- QUOTE.

/- TEXT:
这允许将两个子幺半群的交集作为子幺半群获得。

BOTH: -/

-- QUOTE:
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P
-- QUOTE.

/- TEXT:
你可能会想，在上面的例子中我们不得不使用下确界符号 ``⊓`` 而不是交集符号 ``∩``，这很可惜。但想想上确界。两个子幺半群的并集不是子幺半群。然而，子幺半群仍然形成一个格（甚至是一个完备格）。实际上 ``N ⊔ P`` 是由 ``N`` 和 ``P`` 的并集生成的子幺半群，当然将其记为 ``N ∪ P`` 会非常混淆。所以你可以看到 ``N ⊓ P`` 的使用更加一致。它也在各种代数结构中更加一致。一开始看到两个向量子空间 ``E`` 和 ``F`` 的和被记为 ``E ⊔ F`` 而不是 ``E + F`` 可能会觉得有点奇怪。但你会习惯的。很快你就会认为 ``E + F`` 记号是一种分散注意力的东西，它强调了 ``E ⊔ F`` 的元素可以写成 ``E`` 的一个元素和 ``F`` 的一个元素之和这一轶事性质，而不是强调 ``E ⊔ F`` 是包含 ``E`` 和 ``F`` 的最小子空间这一基本事实。

本章的最后一个主题是商。我们再次想解释 Mathlib 中是如何构建方便的记号以及如何避免代码重复的。这里的主要工具是 ``HasQuotient`` 类，它允许像 ``M ⧸ N`` 这样的记号。注意商符号 ``⧸`` 是一个特殊的 unicode 字符，不是常规的 ASCII 除法符号。

作为示例，我们将构建交换幺半群商掉子幺半群的商，把证明留给你。在最后一个例子中，你可以使用 ``Setoid.refl``，但它不会自动找到相关的 ``Setoid`` 结构。你可以通过使用 ``@`` 语法提供所有参数来解决这个问题，如 ``@Setoid.refl M N.Setoid``。

BOTH: -/

-- QUOTE:
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, mul_comm b, mul_assoc, h', ← mul_assoc, mul_comm z, mul_assoc]
-- BOTH:
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  Quotient := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro a₁ b₁ ⟨w, hw, z, hz, ha⟩ a₂ b₂ ⟨w', hw', z', hz', hb⟩
    refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
    rw [mul_comm w, ← mul_assoc, mul_assoc a₁, hb, mul_comm, ← mul_assoc, mul_comm w, ha,
        mul_assoc, mul_comm z, mul_assoc b₂, mul_comm z', mul_assoc]
-- BOTH:
        )
  mul_assoc := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
-- BOTH:
  one := QuotientMonoid.mk N 1
  one_mul := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [one_mul] ; apply @Setoid.refl M N.Setoid
-- BOTH:
  mul_one := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [mul_one] ; apply @Setoid.refl M N.Setoid
-- QUOTE.
