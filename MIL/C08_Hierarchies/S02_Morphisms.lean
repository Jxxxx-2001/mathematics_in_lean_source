import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_morphisms:

态射
---------

到目前为止，在本章中我们讨论了如何创建数学结构的层级结构。
但定义结构并不算真正完成，直到我们有了态射。这里主要有两种方法。最明显的是在函数上定义一个谓词。
BOTH: -/

-- QUOTE:
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
在这个定义中，使用合取有点不太愉快。特别是用户需要记住我们选择的顺序，当他们想要访问这两个条件的时候。
所以我们可以改用结构体。

BOTH: -/
-- QUOTE:
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
一旦我们走到了这里，甚至诱人地想把它变成一个类，并使用类型类实例解析过程从更简单函数的实例自动推断复杂函数的 ``isMonoidHom₂``。例如，幺半群同态的复合是一个幺半群同态，这似乎是一个有用的实例。然而，这样一个实例对于解析过程来说会非常棘手，因为它需要在各处搜寻 ``g ∘ f``。看到它在 ``g (f x)`` 中失败会非常令人沮丧。更一般地，我们必须时刻牢记，识别表达式中应用的是哪个函数是一个非常困难的问题，被称为"高阶统一问题"（higher-order unification problem）。所以 Mathlib 不使用这种类方法。

一个更根本的问题是，我们是使用如上所述的谓词（使用 ``def`` 或 ``structure``），还是使用将函数和谓词捆绑在一起的结构体。这部分是一个心理问题。考虑一个不是同态的幺半群之间的函数是极其罕见的。
真的感觉"幺半群同态"不是一个你可以赋给一个裸函数的形容词，它是一个名词。另一方面，可以论证拓扑空间之间的连续函数确实是一个碰巧连续的函数。这就是 Mathlib 有一个 ``Continuous`` 谓词的原因之一。例如你可以写：

BOTH: -/
-- QUOTE:
example : Continuous (id : ℝ → ℝ) := continuous_id
-- QUOTE.
/- TEXT:
我们仍然有连续函数的捆绑，这对于在连续函数空间上放置拓扑等是很方便的，但它们并不是处理连续性的主要工具。

相比之下，幺半群（或其他代数结构）之间的态射是捆绑的，如：

BOTH: -/
-- QUOTE:
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- TEXT:
当然我们不想在所有地方都打 ``toFun``，所以我们使用 ``CoeFun`` 类型类注册一个强制转换。它的第一个参数是我们想要强制转换为函数的类型。第二个参数描述目标函数类型。在我们的例子中，对于每个 ``f : MonoidHom₁ G H`` 它总是 ``G → H``。我们还用 ``coe`` 属性标记 ``MonoidHom₁.toFun``，以确保它在策略状态中几乎不可见地显示，仅通过一个 ``↑`` 前缀。

BOTH: -/
-- QUOTE:
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
-- QUOTE.

/- TEXT:
让我们检查一下，我们确实可以将一个捆绑的幺半群同态应用于一个元素。

BOTH: -/

-- QUOTE:
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one
-- QUOTE.
/- TEXT:
我们可以对其他类型的态射做同样的事情，直到达到环同态。

BOTH: -/

-- QUOTE:
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

-- QUOTE.

/- TEXT:
这种方法有几个问题。一个小问题是我们不太知道该把 ``coe`` 属性放在哪里，因为 ``RingHom₁.toFun`` 并不存在，相关的函数是 ``MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁``，这不是一个可以用属性标记的声明（但我们仍然可以定义一个 ``CoeFun (RingHom₁ R S) (fun _ ↦ R → S)`` 实例）。
一个更为重要的问题是，关于幺半群同态的引理不会直接适用于环同态。这留下的选择是：要么每次我们想应用幺半群同态引理时都要摆弄 ``RingHom₁.toMonoidHom₁``，要么为环同态重新陈述每个这样的引理。
两种选择都不吸引人，所以 Mathlib 在这里使用了一种新的层级结构技巧。其思路是定义一个类型类，用于至少是幺半群同态的对象，将此类型类同时实例化在幺半群同态和环同态上，并用它来陈述每个引理。在下面的定义中，如果 ``M`` 和 ``N`` 具有环结构，``F`` 可以是 ``MonoidHom₁ M N``，也可以是 ``RingHom₁ M N``。

BOTH: -/

-- QUOTE:
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
-- QUOTE.

/- TEXT:
然而上述实现有一个问题。我们还没有注册到函数实例的强制转换。现在让我们尝试做这件事。

BOTH: -/

-- QUOTE:
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- QUOTE.

/- TEXT:
将此设为一个实例将是坏的。当面对像 ``f x`` 这样的表达式，且 ``f`` 的类型不是函数类型时，Lean 会尝试寻找一个 ``CoeFun`` 实例将 ``f`` 强制转换为函数。
上述函数的类型为：
``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)``
因此，当它尝试应用它时，Lean 先验地不清楚应该以什么顺序推断未知类型 ``M``、``N`` 和 ``F``。这是一种与我们之前看到的略有不同的坏实例，但归结为同一个问题：在不知道 ``M`` 的情况下，Lean 将不得不在一个未知类型上搜索幺半群实例，从而无望地尝试数据库中的*每一个*幺半群实例。如果你好奇这种实例的效果，你可以在上述声明之上打 ``set_option synthInstance.checkSynthOrder false in``，将 ``def badInst`` 替换为 ``instance``，然后观察此文件中的随机失败。

这里的解决方案很简单，我们需要告诉 Lean 首先搜索 ``F`` 是什么，然后推导出 ``M`` 和 ``N``。这是通过 ``outParam`` 函数完成的。这个函数被定义为恒等函数，但仍然被类型类机制识别并触发所需的行为。
因此我们可以重新尝试定义我们的类，注意 ``outParam`` 函数：
BOTH: -/

-- QUOTE:
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
-- QUOTE.

/- TEXT:
现在我们可以按照计划继续实例化这个类。

BOTH: -/

-- QUOTE:
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
如所承诺的，我们关于 ``f : F``（假设一个 ``MonoidHomClass₁ F`` 的实例）证明的每个引理都将同时适用于幺半群同态和环同态。
让我们看一个示例引理，并检查它是否适用于这两种情况。
BOTH: -/

-- QUOTE:
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- QUOTE.

/- TEXT:
乍一看，可能看起来我们又回到了把 ``MonoidHom₁`` 变成类的旧的坏主意。但我们并没有。一切都向上移动了一个抽象层次。类型类解析过程不会去寻找函数，它将寻找 ``MonoidHom₁`` 或 ``RingHom₁``。

我们的方法剩下的一个问题是围绕 ``toFun`` 字段以及相应的 ``CoeFun`` 实例和 ``coe`` 属性存在重复代码。如果能记录下这种模式仅用于具有额外性质的函数，这意味着到函数的强制转换应该是单射，那也会更好。所以 Mathlib 通过基础类 ``DFunLike``（其中“DFun”代表依赖函数）添加了又一层抽象。
让我们在这个基础层之上重新定义我们的 ``MonoidHomClass``。

BOTH: -/

-- QUOTE:
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
当然，态射的层级结构并不止于此。我们可以继续定义一个扩展 ``MonoidHomClass₃`` 的类 ``RingHomClass₃``，并实例化在 ``RingHom`` 上，然后再实例化在 ``AlgebraHom`` 上（代数是具有一些额外结构的环）。但我们已经涵盖了 Mathlib 中用于态射的主要形式化思想，你应该准备好理解 Mathlib 中态射是如何定义的了。

作为练习，你应该尝试定义你自己的保序函数的捆绑类，以及保序的幺半群同态。这仅用于训练目的。
与连续函数一样，保序函数在 Mathlib 中主要是非捆绑的，它们由 ``Monotone`` 谓词定义。当然，你需要完成下面的类定义。
BOTH: -/

-- QUOTE:
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]
-- SOLUTIONS:
extends DFunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'
-- BOTH:

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
-- SOLUTIONS:
  coe := OrderPresHom.toFun
  coe_injective' _ _ := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
-- SOLUTIONS:
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  le_of_le := fun f ↦ f.toOrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
/- EXAMPLES:
  := sorry
SOLUTIONS: -/
where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.
