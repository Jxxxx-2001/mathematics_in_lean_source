-- BOTH:
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

/- TEXT:
.. _groups:

幺半群与群
------------------

.. index:: monoid
.. index:: group (algebraic structure)

幺半群及其态射
^^^^^^^^^^^^^^^^^^^^^^^^^^^

抽象代数课程通常从群开始，然后逐步推进到环、域和向量空间。这在讨论环上的乘法时会涉及一些周折，因为乘法运算并非来自群结构，但许多证明可以从群论逐字移植到这个新设定中。
最常用的解决方法，在纸上做数学时，是将这些证明留作练习。一种效率较低但更安全、更适合形式化的方法是使用幺半群。类型 `M` 上的*幺半群*（monoid）结构是一个内部的结合运算，并且有一个单位元。
幺半群主要用于同时容纳群和环的乘法结构。但也有许多自然的例子；例如，配备加法的自然数集合就形成一个幺半群。

从实践的角度来看，在使用 Mathlib 时你基本上可以忽略幺半群。但当你在浏览 Mathlib 文件寻找引理时，你需要知道它们的存在。否则，你可能会在群论文件中寻找一个陈述，而它实际上是在幺半群中找到的，因为它不需要元素可逆。

类型 ``M`` 上的幺半群结构的类型写作 ``Monoid M``。
函数 ``Monoid`` 是一个类型类，因此它几乎总是作为实例隐式参数出现（换句话说，在方括号中）。
默认情况下，``Monoid`` 对运算使用乘法记号；对于加法记号，请使用 ``AddMonoid``。
这些结构的交换版本在 ``Monoid`` 前面加上前缀 ``Comm``。
EXAMPLES: -/
-- QUOTE:
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
-- QUOTE.

/- TEXT:
注意，虽然 ``AddMonoid`` 可以在库中找到，但对非交换运算使用加法记号通常是令人困惑的。

幺半群 ``M`` 和 ``N`` 之间的态射类型称为 ``MonoidHom M N``，写作 ``M →* N``。当我们将其应用于 ``M`` 的元素时，Lean 会自动将这样的态射视为从 ``M`` 到 ``N`` 的函数。加法版本称为 ``AddMonoidHom``，写作 ``M →+ N``。
EXAMPLES: -/
-- QUOTE:
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
-- QUOTE.

/- TEXT:
这些态射是捆绑映射（bundled maps），即它们将映射和它的一些性质打包在一起。
请记住 :numref:`section_hierarchies_morphisms` 解释了捆绑映射；
这里我们只需注意一个稍微不幸的后果，即我们不能使用普通的函数复合来复合这些映射。相反，我们需要使用 ``MonoidHom.comp`` 和 ``AddMonoidHom.comp``。
EXAMPLES: -/
-- QUOTE:
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
-- QUOTE.

/- TEXT:
群及其态射
^^^^^^^^^^^^^^^^^^^^^^^^^^

我们将对群有更多的讨论，群是幺半群，并额外具有每个元素都有逆元的性质。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x
-- QUOTE.

/- TEXT:

.. index:: group (tactic), tactics ; group

类似于我们之前看到的 ``ring`` 策略，有一个 ``group`` 策略，它可以证明在任何群中成立的任何恒等式。（等价地，它证明在自由群中成立的恒等式。）

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
-- QUOTE.

/- TEXT:
.. index:: abel, tactics ; abel

对于交换加法群中的恒等式，也有一个策略叫做 ``abel``。

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel
-- QUOTE.

/- TEXT:
有趣的是，群同态无非就是群之间的幺半群同态。所以我们可以复制粘贴前面的一个例子，将 ``Monoid`` 替换为 ``Group``。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y
-- QUOTE.

/- TEXT:
当然，我们确实得到了一些新的性质，比如这个：
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x
-- QUOTE.

/- TEXT:
你可能会担心构造群同态会要求我们做不必要的工作，因为幺半群同态的定义强制要求将单位元映射到单位元，而这在群同态的情况下是自动的。在实践中，这些额外的工作并不困难，但为了避免它，有一个函数可以从一个与复合律兼容的群之间的函数构建群同态。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h
-- QUOTE.

/- TEXT:
还有一个类型 ``MulEquiv`` 表示群（或幺半群）同构，记为 ``≃*``（在加法记号中是 ``AddEquiv``，记为 ``≃+``）。
``f : G ≃* H`` 的逆是 ``MulEquiv.symm f : H ≃* G``，
``f`` 和 ``g`` 的复合是 ``MulEquiv.trans f g``，而
``G`` 的恒等同构是 ``MulEquiv.refl G``。
使用匿名投影记号，前两个可以分别写作 ``f.symm`` 和 ``f.trans g``。
此类型的元素在必要时会自动强制转换为态射和函数。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
可以使用 ``MulEquiv.ofBijective`` 从双射同态构建同构。
这样做会使逆函数不可计算。
EXAMPLES: -/
-- QUOTE:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h
-- QUOTE.

/- TEXT:
子群
^^^^^^^^^

正如群同态是捆绑的，``G`` 的子群也是一个捆绑结构，由 ``G`` 中带有相关闭包性质的集合组成。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx
-- QUOTE.

/- TEXT:
在上面的例子中，重要的是要理解 ``Subgroup G`` 是 ``G`` 的子群的类型，而不是一个谓词 ``IsSubgroup H``，其中 ``H`` 是 ``Set G`` 的一个元素。
``Subgroup G`` 被赋予了到 ``Set G`` 的强制转换和 ``G`` 上的成员关系谓词。
参见 :numref:`section_hierarchies_subobjects` 以了解这是如何以及为什么这样做的解释。

当然，两个子群是相同的当且仅当它们具有相同的元素。这一事实已注册供 ``ext`` 策略使用，该策略可以像用于证明两个集合相等一样用于证明两个子群相等。

为了陈述和证明，例如，``ℤ`` 是 ``ℚ`` 的加法子群，
我们真正想要的是构造一个类型为 ``AddSubgroup ℚ`` 的项，其到
``Set ℚ`` 的投影是 ``ℤ``，或者更精确地说，是 ``ℤ`` 在 ``ℚ`` 中的像。
EXAMPLES: -/
-- QUOTE:
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp
-- QUOTE.

/- TEXT:
使用类型类，Mathlib 知道群的子群继承群结构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance
-- QUOTE.

/- TEXT:
这个例子很微妙。对象 ``H`` 不是一个类型，但 Lean 会自动将其强制转换为类型，通过将其解释为 ``G`` 的子类型。
因此上面的例子可以更显式地重述为：
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
-- QUOTE.

/- TEXT:
拥有类型 ``Subgroup G`` 而不是谓词 ``IsSubgroup : Set G → Prop`` 的一个重要好处是，可以轻松地为 ``Subgroup G`` 赋予额外的结构。
重要的是，它具有关于包含关系的完备格结构。例如，不必有一个引理陈述 ``G`` 的两个子群的交仍是一个子群，我们使用格运算 ``⊓`` 来构造交集。然后我们可以对构造应用关于格的任意引理。

让我们检查一下两个子群的下确界的基础集合，根据定义，确实是它们的交集。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl
-- QUOTE.

/- TEXT:
对于本质上是基础集合交集的东西使用不同的记号可能看起来奇怪，但这种对应关系在上确界运算和集合并集的情况下并不成立，因为子群的并集通常不是子群。
相反，需要使用由并集生成的子群，这通过 ``Subgroup.closure`` 完成。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]
-- QUOTE.

/- TEXT:
另一个微妙之处是 ``G`` 本身不具有类型 ``Subgroup G``，
所以我们需要一种方式来谈论被视为 ``G`` 的子群的 ``G``。
这也可以通过格结构提供：全子群是这个格的顶元素。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
-- QUOTE.

/- TEXT:
类似地，这个格的底元素是其唯一元素为单位元的子群。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot
-- QUOTE.

/- TEXT:
作为操纵群和子群的练习，你可以用外围群的一个元素来定义子群的共轭。
BOTH: -/
-- QUOTE:
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
-- BOTH:
  inv_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
-- BOTH:
  mul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
-- BOTH:
-- QUOTE.

/- TEXT:
将前两个主题联系起来，可以使用群同态向前推进和向后拉回子群。Mathlib 中的命名约定是将这些运算称为 ``map``
和 ``comap``。
这些不是常见的数学术语，但它们比"前推"（pushforward）和"直接像"（direct image）更短。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap
-- QUOTE.

/- TEXT:
特别地，同态 ``f`` 下底子群的原像是一个子群，称为 ``f`` 的*核*（kernel），而 ``f`` 的值域也是一个子群。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range
-- QUOTE.

/- TEXT:
作为操纵群同态和子群的练习，让我们证明一些基本性质。
它们在 Mathlib 中已经被证明过了，所以如果你想从这些练习中受益，不要过快地使用 ``exact?``。
BOTH: -/
-- QUOTE:
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_comap] at * -- Lean 不需要这一行
  exact hST hx
-- BOTH:

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_map] at * -- Lean 不需要这一行
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy
-- BOTH:

variable {K : Type*} [Group K]

-- 记住你可以使用 `ext` 策略来证明子群的相等。
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  -- 整个证明可以是 ``rfl``，但让我们分解一下。
  ext x
  simp only [mem_comap]
  rfl
-- BOTH:

-- 沿一个同态推进一个子群，然后再沿另一个同态推进，等于沿这两个同态的复合向前推进它。
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    calc ψ.comp φ z = ψ (φ z) := rfl
    _               = ψ y := by congr
    _               = x := hy
-- BOTH:

end exercises
-- QUOTE.

/- TEXT:
让我们用两个非常经典的结果来结束对 Mathlib 中子群的介绍。
拉格朗日定理陈述了有限群的子群的基数整除该群的基数。Sylow 第一定理是拉格朗日定理的著名部分逆定理。

虽然 Mathlib 的这个角落部分是为了允许计算而设置的，但我们可以使用以下 ``open scoped`` 命令告诉 Lean 无论如何使用非构造性逻辑。
BOTH: -/
-- QUOTE:
open scoped Classical

-- EXAMPLES:

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

-- BOTH:
open Subgroup

-- EXAMPLES:
example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- QUOTE.

/- TEXT:
接下来的两个练习推导出拉格朗日引理的一个推论。（这在 Mathlib 中也已经有了，所以不要过快地使用 ``exact?``。）
BOTH: -/
-- QUOTE:
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨y, -, hy'⟩ x hx
    calc x = y := hy' x hx
    _      = 1 := (hy' 1 H.one_mem).symm
-- EXAMPLES:

#check card_dvd_of_le
-- BOTH:

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have D₁ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  exact eq_bot_iff_card.2 (Nat.eq_one_of_dvd_coprimes h D₁ D₂)
-- QUOTE.

/- TEXT:
具体群
^^^^^^^^^^^^^^^

在 Mathlib 中也可以操作具体的群，尽管这通常比处理抽象理论更复杂。
例如，给定任意类型 ``X``，``X`` 的置换群是 ``Equiv.Perm X``。
特别地，对称群 :math:`\mathfrak{S}_n` 是 ``Equiv.Perm (Fin n)``。
可以陈述关于此群的抽象结果，例如若 ``X`` 有限，则 ``Equiv.Perm X`` 由循环生成。
EXAMPLES: -/
-- QUOTE:
open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle
-- QUOTE.

/- TEXT:
可以完全具体地计算循环的实际乘积。下面我们使用 ``#simp`` 命令，
它在给定表达式上调用 ``simp`` 策略。记号 ``c[]`` 用于定义一个循环置换。在这个例子中，结果是一个 ``ℕ`` 的置换。可以在出现的第一个数字上使用类型标注，如 ``(1 : Fin 5)``，使其成为 ``Perm (Fin 5)`` 中的计算。
EXAMPLES: -/
-- QUOTE:
#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]
-- QUOTE.

/- TEXT:
另一种处理具体群的方法是使用自由群和群展示。
类型 ``α`` 上的自由群是 ``FreeGroup α``，包含映射是
``FreeGroup.of : α → FreeGroup α``。例如，让我们定义一个类型 ``S``，它有三个元素，记作
``a``、``b`` 和 ``c``，以及相应自由群的元素 ``ab⁻¹``。
EXAMPLES: -/
-- QUOTE:
section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹
-- QUOTE.

/- TEXT:
注意我们给出了定义的期望类型，以便 Lean 知道 ``.of`` 的意思是 ``FreeGroup.of``。

自由群的泛性质体现为等价 ``FreeGroup.lift``。
例如，让我们定义从 ``FreeGroup S`` 到 ``Perm (Fin 5)`` 的群同态，将
``a`` 映为 ``c[1, 2, 3]``，``b`` 映为 ``c[2, 3, 1]``，``c`` 映为 ``c[2, 3]``。
EXAMPLES: -/
-- QUOTE:
def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]

-- QUOTE.

/- TEXT:
作为最后一个具体例子，让我们看看如何定义一个由一个元素生成的群，其立方为单位元（因此该群将同构于 :math:`\mathbb{Z}/3`），并构建从该群到 ``Perm (Fin 5)`` 的同态。

作为恰好有一个元素的类型，我们将使用 ``Unit``，其唯一元素记为 ``()``。函数 ``PresentedGroup`` 接受一组关系，即某个自由群的元素集合，并返回一个群，该群是这个自由群商掉由关系生成的正规子群。（我们将在 :numref:`quotient_groups` 中看到如何处理更一般的商。）由于我们以某种方式将其隐藏在定义后面，我们使用 ``deriving Group`` 来强制创建 ``myGroup`` 上的群实例。
EXAMPLES: -/
-- QUOTE:
def myGroup := PresentedGroup {.of () ^ 3} deriving Group
-- QUOTE.

/- TEXT:
展示群的泛性质确保，从该群出发的同态可以从将关系映到目标群的单位元的函数构建。
所以我们需要这样一个函数和一个证明条件成立的证明。然后我们可以将这个证明
提供给 ``PresentedGroup.toGroup`` 以获得所需的群同态。
EXAMPLES: -/
-- QUOTE:
def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup
-- QUOTE.

/- TEXT:
群作用
^^^^^^^^^^^^^

群论与数学其余部分相互作用的一个重要方式是通过群作用的使用。
群 ``G`` 在某个类型 ``X`` 上的作用无非是从 ``G`` 到 ``Equiv.Perm X`` 的同态。所以从某种意义上说，群作用已经被前面的讨论涵盖了。
但我们不想随身携带这个同态；相反，我们希望它尽可能被 Lean 自动推断。所以我们有一个类型类 ``MulAction G X``。
这种设置的缺点是，同一个群在同一类型上具有多个作用需要一些周折，例如定义类型同义词，每个都携带不同的类型类实例。

这特别允许我们使用 ``g • x`` 来表示群元素 ``g`` 对点 ``x`` 的作用。
BOTH: -/
-- QUOTE:
noncomputable section GroupActions

-- EXAMPLES:
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
-- QUOTE.

/- TEXT:
对于加法群也有一个版本叫做 ``AddAction``，其中的作用记为 ``+ᵥ``。这用于例如仿射空间的定义中。
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm
-- QUOTE.

/- TEXT:
底层的群同态称为 ``MulAction.toPermHom``。
EXAMPLES: -/
-- QUOTE:
open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X
-- QUOTE.

/- TEXT:
作为说明，让我们看看如何定义任意群 ``G`` 到置换群 ``Perm G`` 的 Cayley 同构嵌入。
EXAMPLES: -/
-- QUOTE:
def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G
-- QUOTE.

/- TEXT:
注意，上述定义之前的一切都不需要群而不只是幺半群（或者任何真正配备了乘法运算的类型）。

群条件真正进入视野是当我们想要将 ``X`` 划分为轨道时。
``X`` 上相应的等价关系称为 ``MulAction.orbitRel``。
它没有被声明为全局实例。
EXAMPLES: -/
/- OMIT:
TODO: 我们需要在某个地方解释一下 `Setoid`。
EXAMPLES. -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X
-- QUOTE.

/- TEXT:
利用这一点，我们可以陈述 ``X`` 在 ``G`` 的作用下被划分为轨道。
更精确地说，我们得到 ``X`` 与依赖积
``(ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω))`` 之间的双射，
其中 ``Quotient.out' ω`` 简单地选择一个投影到 ``ω`` 的元素。
回忆一下，这个依赖积的元素是形如 ``⟨ω, x⟩`` 的对，其中 ``x`` 的类型 ``orbit G (Quotient.out' ω)`` 依赖于 ``ω``。
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out ω)) :=
  MulAction.selfEquivSigmaOrbits G X
-- QUOTE.

/- TEXT:
特别地，当 X 有限时，这可以与 ``Fintype.card_congr`` 和 ``Fintype.card_sigma`` 结合，推出 ``X`` 的基数是轨道基数之和。
此外，轨道与 ``G`` 在稳定子群的左平移作用下的商之间存在双射。
子群通过左平移的作用用于定义群商掉子群的商，记号是 `/`，因此我们可以使用以下简洁的陈述。
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x
-- QUOTE.

/- TEXT:
结合上述两个结果的一个重要特例是当 ``X`` 是群 ``G`` 本身，配备了子群 ``H`` 平移作用时。
在这种情况下，所有稳定子群都是平凡的，所以每个轨道都与 ``H`` 双射，我们得到：
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup
-- QUOTE.

/- TEXT:
这是我们上面看到的拉格朗日定理版本的概念性变体。注意这个版本不做有限性假设。

作为本节的练习，让我们使用前面练习中对 ``conjugate`` 的定义，构建群在其子群上的共轭作用。
BOTH: -/
-- QUOTE:
variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp [conjugate]
-- BOTH:

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact conjugate_one
-- BOTH:
  mul_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro x y H
    ext z
    constructor
    · rintro ⟨h, h_in, rfl⟩
      use y*h*y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
      use h, h_in
      group
-- BOTH:

end GroupActions
-- QUOTE.

/- TEXT:
.. _quotient_groups:

商群
^^^^^^^^^^^^^^^

在上面对子群作用于群的讨论中，我们看到了商 ``G ⧸ H`` 的出现。
一般来说，这只是一个类型。它可以被赋予一个群结构，使得商映射是一个群同态，当且仅当 ``H`` 是一个正规子群（并且这个群结构是唯一的）。

正规性假设是一个类型类 ``Subgroup.Normal``，因此类型类推断可以使用它来推导商上的群结构。
BOTH: -/
-- QUOTE:
noncomputable section QuotientGroup

-- EXAMPLES:
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
-- QUOTE.

/- TEXT:
商群的泛性质通过 ``QuotientGroup.lift`` 访问：
群同态 ``φ`` 只要它的核包含 ``N``，就可以下降到 ``G ⧸ N``。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h
-- QUOTE.

/- TEXT:
在上述代码片段中，目标群被称为 ``M`` 这一事实暗示了，在 ``M`` 上有幺半群结构就足够了。

一个重要的特例是当 ``N = ker φ`` 时。在这种情况下，下降的同态是单射，我们得到到其像的群同构。这个结果通常被称为第一同构定理。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
-- QUOTE.

/- TEXT:
将泛性质应用于同态 ``φ : G →* G'`` 与商群投影 ``Quotient.mk' N'`` 的复合，
我们也可以得到从 ``G ⧸ N`` 到 ``G' ⧸ N'`` 的同态。
对 ``φ`` 所需的条件通常被表述为"``φ`` 应将 ``N`` 送入 ``N'`` 中"。但这等价于要求 ``φ`` 应将 ``N'`` 拉回到包含 ``N`` 的条件，而后者更容易处理，因为拉回的定义不涉及存在量词。
EXAMPLES: -/
-- QUOTE:
example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h
-- QUOTE.

/- TEXT:
需要记住的一个微妙点是，类型 ``G ⧸ N`` 确实依赖于 ``N``
（直到定义相等），所以有一个证明两个正规子群 ``N`` 和 ``M`` 相等是不够的，不能使相应的商相等。然而，泛性质确实在这种情况下给出了一个同构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
-- QUOTE.

/- TEXT:
作为本节最后的一系列练习，我们将证明，如果 ``H`` 和 ``K`` 是有限群 ``G`` 的不相交的正规子群，且它们的基数的乘积等于 ``G`` 的基数，
那么 ``G`` 同构于 ``H × K``。回忆一下，在此上下文中，不相交意味着 ``H ⊓ K = ⊥``。

我们从稍微玩一下拉格朗日引理开始，不假设子群是正规的或不相交的。
BOTH: -/
-- QUOTE:
section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- 非空参数对于子群会被自动推断
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := calc
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by rw [← H.index_eq_card, H.index_mul_card]
    _                             = Nat.card K * Nat.card H := by rw [h', mul_comm]

  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
-- QUOTE.

/- TEXT:
从现在开始，我们假设我们的子群是正规且不相交的，并假设基数条件。现在我们构造所需同构的第一个构件。
BOTH: -/
-- QUOTE:
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ : K ≃* G ⧸ H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp [h]
  · symm
    exact aux_card_eq h'
-- QUOTE.

/- TEXT:
现在我们可以定义我们的第二个构件。
我们将需要 ``MonoidHom.prod``，它从到 ``G₁`` 和 ``G₂`` 的同态构建从 ``G₀`` 到 ``G₁ × G₂`` 的同态。
BOTH: -/
-- QUOTE:
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' H)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H) _▸ h'), h']
-- QUOTE.

/- TEXT:
我们准备好将所有部分组合在一起了。
EXAMPLES: -/
-- QUOTE:
#check MulEquiv.prodCongr

-- BOTH:
def finalIso : G ≃* H × K :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm

end
end QuotientGroup
-- QUOTE.
