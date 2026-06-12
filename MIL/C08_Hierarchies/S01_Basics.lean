import MIL.Common
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_basics:

基础知识
------

在 Lean 中所有层级的最底层，我们找到的是承载数据的类。下面的类记录了给定类型 ``α`` 具有一个称为 ``one`` 的特定元素。在这个阶段，它还没有任何性质。
BOTH: -/

-- QUOTE:
class One₁ (α : Type) where
  /-- 元素 one -/
  one : α
-- QUOTE.

/- TEXT:
由于我们在本章中将更大量地使用类，我们需要更详细地了解 ``class`` 命令到底做了什么。
首先，上面的 ``class`` 命令定义了一个带有参数 ``α : Type`` 和单个字段 ``one`` 的结构体 ``One₁``。它还将此结构体标记为类，这样对于某个类型 ``α`` 的参数 ``One₁ α`` 就可以通过实例解析过程来推断，只要它们被标记为实例隐式参数（即出现在方括号中）。
这两种效果也可以通过使用带有 ``class`` 属性的 ``structure`` 命令来实现，即写成 ``@[class] structure`` 而不是 ``class``。但 class 命令还确保 ``One₁ α`` 在其自身的字段中作为实例隐式参数出现。请比较：
BOTH: -/

-- QUOTE:
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- 元素 one -/
  one : α

#check One₂.one
-- QUOTE.

/- TEXT:
在第二次检查中，我们可以看到 ``self : One₂ α`` 是一个显式参数。
让我们确保第一个版本确实可以在没有任何显式参数的情况下使用。
BOTH: -/

-- QUOTE:
example (α : Type) [One₁ α] : α := One₁.one
-- QUOTE.

/- TEXT:
备注：在上面的例子中，参数 ``One₁ α`` 被标记为实例隐式参数，这有点傻，因为这只会影响声明的*使用*，而 ``example`` 命令创建的声明是不能被使用的。然而，它使我们能够避免给该参数命名，更重要的是，它开始培养将 ``One₁ α`` 参数标记为实例隐式参数的好习惯。

另一个备注是，所有这些只有在 Lean 知道 ``α`` 是什么时才会工作。在上面的例子中，省略类型标注 ``: α`` 会产生类似这样的错误信息：
``typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)``
其中 ``?m.263 α`` 的意思是"某个依赖于 ``α`` 的类型"（263 只是一个自动生成的索引，用于区分多个未知的事物）。另一种避免此问题的方法是使用类型标注，如：
BOTH: -/
-- QUOTE:
example (α : Type) [One₁ α] := (One₁.one : α)
-- QUOTE.

/- TEXT:
你可能已经在 :numref:`sequences_and_convergence` 中玩序列极限时遇到过了这个问题，如果你尝试声明 ``0 < 1`` 而没有告诉 Lean 这个不等式是关于自然数还是实数的话。

我们的下一个任务是为 ``One₁.one`` 分配一个记号。由于我们不想与内置的 ``1`` 记号冲突，我们将使用 ``𝟙``。这是通过以下命令实现的，其中第一行告诉 Lean 使用 ``One₁.one`` 的文档作为符号 ``𝟙`` 的文档。
BOTH: -/
-- QUOTE:
@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
-- QUOTE.

/- TEXT:
现在我们想要一个记录二元运算的数据类。现在我们还不想在加法和乘法之间做选择，所以我们将使用菱形。
BOTH: -/

-- QUOTE:
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
-- QUOTE.

/- TEXT:
如同 ``One₁`` 的例子，这个运算在这个阶段还没有任何性质。现在让我们定义半群结构的类，其中运算用 ``⋄`` 表示。
现在，我们手工将其定义为一个具有两个字段的结构体：一个 ``Dia₁`` 实例和一个取值为 ``Prop`` 的字段 ``dia_assoc``，它断言 ``⋄`` 的结合律。
BOTH: -/

-- QUOTE:
class Semigroup₀ (α : Type) where
  toDia₁ : Dia₁ α
  /-- 菱形运算是结合的 -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- TEXT:
注意，在声明 `dia_assoc` 时，之前定义的字段 `toDia₁` 在局部上下文中，因此当 Lean 搜索 `Dia₁ α` 的实例以解释 `a ⋄ b` 的含义时可以使用它。然而，这个 `toDia₁` 字段并不会成为类型类实例数据库的一部分。
因此，执行 ``example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b`` 时会失败，并显示错误信息 ``failed to synthesize instance Dia₁ α``。

我们可以通过之后添加 ``instance`` 属性来修复这个问题。
BOTH: -/

-- QUOTE:
attribute [instance] Semigroup₀.toDia₁

example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
在继续构建之前，我们需要使用一种不同的语法来添加这个 `toDia₁` 字段，以告诉 Lean `Dia₁ α` 应该被视为 `Semigroup₁` 自身的字段一样来处理。
这也方便地自动添加了 `toDia₁` 实例。
``class`` 命令支持使用 ``extends`` 语法来实现这一点，如：
BOTH: -/

-- QUOTE:
class Semigroup₁ (α : Type) extends toDia₁ : Dia₁ α where
  /-- 菱形运算是结合的 -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
注意，这种语法在 ``structure`` 命令中也可用，尽管在这种情况下它只解决了编写 `toDia₁` 等字段的麻烦，因为在那种情况下没有要定义的实例。

`toDia₁` 字段名在 `extends` 语法中是可选的。
默认情况下，它取被扩展的类的名称并在前面加上 "to"。
BOTH: -/

-- QUOTE:
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- 菱形运算是结合的 -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- TEXT:
现在让我们尝试将菱形运算和特定的一元元素结合起来，并加上断言此元素是双边单位元的公理。
BOTH: -/
-- QUOTE:
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- 壹是菱形运算的左单位元. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- 壹是菱形运算的右单位元 -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- QUOTE.

/- TEXT:
在下一个例子中，我们告诉 Lean ``α`` 具有 ``DiaOneClass₁`` 结构，并陈述一个同时使用 `Dia₁` 实例和 `One₁` 实例的性质。为了观察 Lean 如何找到这些实例，我们设置了一个追踪选项，其结果可以在信息视图中看到。这个结果默认情况下相当简略，但可以通过点击以黑色箭头结尾的行来展开。
它包括 Lean 在有足够的类型信息成功之前尝试查找实例的失败尝试。成功的尝试确实涉及由 ``extends`` 语法生成的实例。
BOTH: -/

-- QUOTE:
set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
-- QUOTE.

/- TEXT:
注意，我们在组合现有类时不需要包含额外的字段。因此我们可以将幺半群定义为：
BOTH: -/

-- QUOTE:
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
-- QUOTE.

/- TEXT:
虽然上述定义看起来很简单，但它隐藏了一个重要的微妙之处。``Semigroup₁ α`` 和 ``DiaOneClass₁ α`` 都扩展了 ``Dia₁ α``，所以有人可能会担心，拥有一个 ``Monoid₁ α`` 实例会在 ``α`` 上给出两个不相关的菱形运算：一个来自字段 ``Monoid₁.toSemigroup₁``，另一个来自字段 ``Monoid₁.toDiaOneClass₁``。

事实上，如果我们尝试手工构建一个幺半群类，使用：
BOTH: -/

-- QUOTE:
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
-- QUOTE.

/- TEXT:
那么我们会得到两个完全不相关的菱形运算
``Monoid₂.toSemigroup₁.toDia₁.dia`` 和 ``Monoid₂.toDiaOneClass₁.toDia₁.dia``。

使用 ``extends`` 语法生成的版本没有这个缺陷。
BOTH: -/

-- QUOTE:
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
-- QUOTE.

/- TEXT:
所以 ``class`` 命令为我们做了一些魔法（``structure`` 命令也会这样做）。一个查看我们类的字段是什么的简单方法是检查它们的构造函数。请比较：
BOTH: -/

-- QUOTE:
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
-- QUOTE.

/- TEXT:
所以我们看到 ``Monoid₁`` 如预期那样接受 ``Semigroup₁ α`` 参数，但它不会接受可能重叠的 ``DiaOneClass₁ α`` 参数，而是将其拆开，只包含不重叠的部分。它还自动生成了一个实例 ``Monoid₁.toDiaOneClass₁``，它*不是*一个字段，但具有预期的签名，从最终用户的角度来看，它恢复了两个扩展类 ``Semigroup₁`` 和 ``DiaOneClass₁`` 之间的对称性。
BOTH: -/

-- QUOTE:
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
-- QUOTE.

/- TEXT:
我们现在非常接近定义群了。我们可以在幺半群结构中添加一个断言每个元素都存在逆元的字段。但那时我们需要努力去访问这些逆元。在实践中，将其作为数据添加更方便。为了优化可重用性，我们定义一个新的承载数据的类，然后给它一些记号。
BOTH: -/

-- QUOTE:
class Inv₁ (α : Type) where
  /-- 求逆函数 -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
-- QUOTE.

/- TEXT:
上述定义可能看起来太弱了，我们只要求 ``a⁻¹`` 是 ``a`` 的左逆元。
但另一边是自动成立的。为了证明这一点，我们需要一个预备引理。
BOTH: -/

-- QUOTE:
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]
-- QUOTE.

/- TEXT:
在这个引理中，使用全名是相当烦人的，特别是因为这需要知道层级结构的哪一部分提供了那些事实。解决这个问题的一种方法是使用 ``export`` 命令将这些事实作为引理复制到根命名空间中。
BOTH: -/

-- QUOTE:
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)
-- QUOTE.

/- TEXT:
然后我们可以将上述证明重写为：
BOTH: -/

-- QUOTE:
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]
-- QUOTE.

/- TEXT:
现在轮到你来证明关于我们代数结构的一些事情了。
BOTH: -/

-- QUOTE:
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv₁ (inv_dia a) h
-- BOTH:

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  by rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]
-- QUOTE.

/- TEXT:
在这个阶段，我们想继续定义环，但有一个严重的问题。
一个类型上的环结构既包含加法群结构，也包含乘法幺半群结构，还包含关于它们相互作用的一些性质。但到目前为止，我们为所有运算硬编码了一个记号 ``⋄``。更根本的是，类型类系统假设每个类型对于每种类型类只有一个实例。有多种方法可以解决这个问题。令人惊讶的是，Mathlib 使用了一种朴素的想法：借助一些代码生成属性，为加法理论和乘法理论复制所有内容。结构体和类在加法和乘法记号中都有定义，并通过一个 ``to_additive`` 属性将它们关联起来。在多重继承的情况下，比如半群，自动生成的"恢复对称性"实例也需要被标记。
这有点技术性；你不需要理解细节。重要的一点是，引理只以乘法记号陈述，并标记 ``to_additive`` 属性以生成加法版本，如 ``left_inv_eq_right_inv'`` 及其自动生成的加法版本 ``left_neg_eq_right_neg'``。为了检查这个加法版本的名称，我们在 ``left_inv_eq_right_inv'`` 之上使用了 ``whatsnew in`` 命令。
BOTH: -/

-- QUOTE:



class AddSemigroup₃ (α : Type) extends Add α where
  /-- 加法是结合的 -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  /-- 乘法是结合的 -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- TEXT:
有了这项技术，我们也可以轻松地定义交换半群、幺半群和群，进而定义环。

BOTH: -/
-- QUOTE:
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
-- QUOTE.

/- TEXT:
我们应该记得在适当的时候用 ``simp`` 标记引理。
BOTH: -/

-- QUOTE:
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

-- QUOTE.

/- TEXT:
然后我们需要稍微重复一下自己，因为我们切换到了标准记号，但至少 ``to_additive`` 做了从乘法记号到加法记号的翻译工作。
BOTH: -/

-- QUOTE:
@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv' (Group₃.inv_mul a) h
-- BOTH:
-- QUOTE.

/- TEXT:
注意，``to_additive`` 可以被要求用 ``simp`` 标记一个引理，并将该属性传播到加法版本，如下所示。
BOTH: -/

-- QUOTE:
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] (a : G) : a * a⁻¹ = 1 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]
-- BOTH:

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [← mul_assoc₃] using congr_arg (a⁻¹ * ·) h
-- BOTH:

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h
-- BOTH:

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

-- QUOTE.

/- TEXT:
我们现在准备好定义环了。为了演示目的，我们将不假设加法是交换的，然后立即提供一个 ``AddCommGroup₃`` 的实例。Mathlib 不会玩这种把戏，首先是因为在实践中这并不会使任何环实例变得更容易，其次是因为 Mathlib 的代数层级结构会经过半环（semirings），半环类似于环但没有相反元素，所以下面的证明对它们不适用。我们在这里得到的，除了一个你没见过的不错的练习之外，还是一个使用允许将父结构作为实例参数提供然后再提供额外字段的语法来构建实例的例子。
这里，`Ring₃ R` 参数提供了除 `add_comm` 之外 ``AddCommGroup₃ R`` 所想要的一切。
BOTH: -/

-- QUOTE:
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- 乘法对加法有左分配律 -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- 乘法对加法有右分配律 -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ add_comm := by
/- EXAMPLES:
    sorry }
SOLUTIONS: -/
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := calc
      a + (a + b + b) = (a + a) + (b + b) := by simp [add_assoc₃, add_assoc₃]
      _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
      _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
      _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
      _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
      _ = (a + b) + (a + b) := by simp
      _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this) }
-- QUOTE.
/- TEXT:
当然我们也可以构建具体的实例，比如整数上的环结构（当然下面的实例使用了 Mathlib 中已经完成的所有工作）。
BOTH: -/

-- QUOTE:
instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- QUOTE.
/- TEXT:
作为练习，你现在可以为序关系建立一个简单的层级结构，包括一个有序交换幺半群的类，它同时具有偏序和交换幺半群结构，且满足 ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b``。当然你需要向以下类添加字段，也许还需要 ``extends`` 子句。
BOTH: -/
-- QUOTE:

class LE₁ (α : Type) where
  /-- 小于等于关系. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)
-- SOLUTIONS:
  extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
-- BOTH:

class PartialOrder₁ (α : Type)
-- SOLUTIONS:
  extends Preorder₁ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b
-- BOTH:

class OrderedCommMonoid₁ (α : Type)
-- SOLUTIONS:
  extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b
-- BOTH:

instance : OrderedCommMonoid₁ ℕ where
-- SOLUTIONS:
  le := (· ≤ ·)
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ ↦ le_trans
  le_antisymm := fun _ _ ↦ le_antisymm
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := fun _ _ h c ↦ Nat.mul_le_mul_left c h
-- QUOTE.
/- TEXT:



现在我们想讨论涉及多种类型的代数结构。最典型的例子是环上的模。如果你不知道什么是模，你可以假装它指的是向量空间，并认为我们所有的环都是域。这些结构是带有某个环中元素标量乘法的交换加法群。

我们首先定义某个类型 ``α`` 在某个类型 ``β`` 上的标量乘法的数据承载类型类，并赋予它右结合的记号。
BOTH: -/

-- QUOTE:
class SMul₃ (α : Type) (β : Type) where
  /-- 标量乘法 -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
-- QUOTE.

/- TEXT:
然后我们可以定义模（再次强调，如果你不知道什么是模，就把它想成向量空间）。
BOTH: -/

-- QUOTE:
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
-- QUOTE.

/- TEXT:
这里有一些有趣的事情发生。虽然 ``R`` 上的环结构是这个定义中的一个参数并不太令人惊讶，但你可能期望 ``AddCommGroup₃ M`` 是 ``extends`` 子句的一部分，就像 ``SMul₃ R M`` 那样。尝试这样做会导致字段 ``Module₃.toAddCommGroup₃`` 被标记为实例。这个实例将具有签名：
``(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M``。
有了这样的实例在类型类数据库中，每次 Lean 为某个 ``M`` 寻找 ``AddCommGroup₃ M`` 实例时，它都需要去搜寻一个完全未指定的类型 ``R`` 和一个 ``Ring₃ R`` 实例，然后才能开始寻找 ``Module₁ R M`` 实例的主要任务。这两个支线任务由错误信息中提到的元变量表示，并在那里用 ``?R`` 和 ``?inst✝`` 表示。这样的 ``Module₃.toAddCommGroup₃`` 实例将成为实例解析过程的一个巨大陷阱。

那么 ``extends SMul₃ R M`` 呢？那个创建了字段
``Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M``
其最终结果 ``SMul₃ R M`` 同时提到了 ``R`` 和 ``M``，因此这个字段可以安全地用作实例。规则很容易记住：每个出现在 ``extends`` 子句中的类都应该提到参数中出现的每一个类型。

让我们创建我们的第一个模实例：一个环通过其乘法作为标量乘法，是自身上的模。
BOTH: -/
-- QUOTE:
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib
-- QUOTE.
/- TEXT:
作为第二个例子，每个交换群都是 ``ℤ`` 上的模（这是通过允许不可逆标量来推广向量空间理论的原因之一）。首先，可以为任何配备了零和加法的类型定义自然数标量乘法：
``n • a`` 定义为 ``a + ⋯ + a``，其中 ``a`` 出现 ``n`` 次。然后将其扩展到整数标量乘法，通过确保 ``(-1) • a = -a``。
BOTH: -/
-- QUOTE:

def nsmul₁ {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
-- QUOTE.
/- TEXT:
证明这会产生一个模结构是有些繁琐的，并且对于当前的讨论不感兴趣，所以我们将对所有公理使用 sorry。你*不*被要求用证明替换这些 sorries。如果你坚持要这样做，那么你可能需要陈述并证明一些关于 ``nsmul₁`` 和 ``zsmul₁`` 的中间引理。
BOTH: -/
-- QUOTE:

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- QUOTE.
/- TEXT:
一个更为重要的问题是，我们现在对 ``ℤ`` 自身有两个模结构：``abGrpModule ℤ`` 因为 ``ℤ`` 是一个交换群，以及 ``selfModule ℤ`` 因为 ``ℤ`` 是一个环。这两个模结构对应于同一个交换群结构，但它们是否具有相同的标量乘法并不明显。它们实际上有，但这并不是根据定义成立的，它需要一个证明。这对类型类实例解析过程来说是非常坏的消息，并将导致这个层级结构的用户遭遇非常令人沮丧的失败。当直接要求寻找一个实例时，Lean 会选择一个，我们可以使用以下命令看到是哪一个：
BOTH: -/
-- QUOTE:

#synth Module₁ ℤ ℤ -- abGrpModule ℤ

-- QUOTE.
/- TEXT:
但在更间接的上下文中，Lean 可能会推断出另一个，然后就会感到困惑。
这种情况被称为坏菱形。这和我们上面使用的菱形运算无关，它指的是从 ``ℤ`` 出发到其 ``Module₁ ℤ`` 的路径可以通过 ``AddCommGroup₃ ℤ`` 或 ``Ring₃ ℤ`` 绘制的图形。

重要的是要理解，并非所有菱形都是坏的。事实上，Mathlib 中到处都是菱形，本章中也是如此。在最初的开始，我们就看到可以从 ``Monoid₁ α`` 通过 ``Semigroup₁ α`` 或 ``DiaOneClass₁ α`` 到达 ``Dia₁ α``，并且由于 ``class`` 命令所做的工作，得到的两个 ``Dia₁ α`` 实例是定义相等的。特别地，底部是 ``Prop`` 值类的菱形不可能是坏的，因为同一陈述的任何两个证明都是定义相等的。

但我们用模创建的这个菱形绝对是坏的。问题出在 ``smul`` 字段上，它是数据，不是证明，而我们有两个不是定义相等的构造。
修复这个问题的稳健方法是确保从丰富结构到贫乏结构的过程总是通过遗忘数据来完成，而不是通过定义数据来完成。这种众所周知的模式被称为"遗忘继承"（forgetful inheritance），并在
https://inria.hal.science/hal-02463336v2 中有广泛讨论。

在我们的具体情况中，我们可以修改 ``AddMonoid₃`` 的定义，以包含一个 ``nsmul`` 数据字段和一些 ``Prop`` 值字段，确保这个运算在可证明的意义上等同于我们上面构造的运算。这些字段在下面定义中的类型后面使用 ``:=`` 给出了默认值。
得益于这些默认值，大多数实例的构造方式将与我们之前的定义完全相同。但在 ``ℤ`` 的特殊情况下，我们将能够提供特定的值。
BOTH: -/
-- QUOTE:

class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- 自然数乘法. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- 乘以 `(0 : ℕ)` 得到 `0`。 -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- 乘以 `(n + 1 : ℕ)` 的行为符合预期。 -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
-- QUOTE.
/- TEXT:

让我们检查一下，我们仍然可以在不提供 ``nsmul`` 相关字段的情况下构造一个积幺半群实例。
BOTH: -/
-- QUOTE:

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
-- QUOTE.
/- TEXT:
现在让我们处理 ``ℤ`` 的特殊情况，其中我们想使用 ``ℕ`` 到 ``ℤ`` 的强制转换和 ``ℤ`` 上的乘法来构建 ``nsmul``。特别注意，证明字段比上面的默认值包含更多的工作。
BOTH: -/
-- QUOTE:

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
-- QUOTE.
/- TEXT:
让我们检查一下我们是否解决了问题。因为 Lean 已经有自然数和整数的标量乘法定义，而我们想确保我们的实例被使用，我们将不使用 ``•`` 记号，而是调用 ``SMul.mul`` 并显式提供我们上面定义的实例。
BOTH: -/
-- QUOTE:

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- QUOTE.
/- TEXT:
这个故事随后会继续，将 ``zsmul`` 字段纳入群的定义中，以及类似的技巧。你现在已经准备好去阅读 Mathlib 中关于幺半群、群、环和模的定义了。它们比我们在这里看到的更复杂，因为它们是一个庞大层级结构的一部分，但所有的原理都已经在上面解释过了。

作为练习，你可以回到上面构建的序关系层级结构，尝试纳入一个类型类 ``LT₁``，它承载着小于记号 ``<₁``，并确保每个预序都带有一个从 ``≤₁`` 和 ``Prop`` 值字段构建的具有默认值的 ``<₁``，该字段断言这两个比较运算符之间的自然关系。
TEXT. -/

-- SOLUTIONS:
class LT₁ (α : Type) where
  /-- 小于关系 -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class PreOrder₂ (α : Type) extends LE₁ α, LT₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
  lt := fun a b ↦ a ≤₁ b ∧ ¬b ≤₁ a
  lt_iff_le_not_le : ∀ a b : α, a <₁ b ↔ a ≤₁ b ∧ ¬b ≤₁ a := by intros; rfl
