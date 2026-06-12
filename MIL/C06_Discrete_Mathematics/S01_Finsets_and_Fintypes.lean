import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators

/- TEXT:
.. _finsets_and_fintypes:

有限集与有限类型
--------------------

在 Mathlib 中处理有限集和有限类型可能会让人困惑，因为库提供了
多种处理它们的方式。在本节中，我们将讨论最常见的方式。

我们已经在 :numref:`section_induction_and_recursion`
和 :numref:`section_infinitely_many_primes` 中遇到过 ``Finset`` 类型。
顾名思义，类型 ``Finset α`` 的一个元素是类型 ``α`` 元素的一个有限集。
我们将称它们为"有限集"。
``Finset`` 数据类型被设计为具有计算性解释，
许多 ``Finset α`` 上的基本操作假设 ``α`` 具有可判定的相等性，
这保证了存在一个算法来检测 ``a : α`` 是否是
有限集 ``s`` 的元素。
EXAMPLES: -/
-- QUOTE:
section
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end
-- QUOTE.

/- TEXT:
如果你去掉声明 ``[DecidableEq α]``，Lean 会在
``#check s ∩ t`` 这一行报错，因为它无法计算交集。
然而，所有你期望能够计算的
数据类型都具有可判定的相等性，
如果你通过打开 ``Classical`` 命名空间并
声明 ``noncomputable section`` 来经典地工作，你可以对任意类型的元素的有限集
进行推理。

有限集支持集合的大多数集合论运算：
EXAMPLES: -/
-- QUOTE:
open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp only [mem_inter, mem_union]; tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by rw [inter_union_distrib_left]
-- QUOTE.

/- TEXT:
请注意，我们打开了 ``Finset`` 命名空间，
其中可以找到有限集特有的定理。
如果你逐步执行下面最后一个例子，你会看到应用 ``ext``
然后 ``simp`` 将恒等式归结为
命题逻辑中的一个问题。
作为练习，你可以尝试证明来自
:numref:`Chapter %s <sets_and_functions>` 的一些集合恒等式，迁移到有限集上。

你已经见过记号 ``Finset.range n`` 表示
自然数的有限集 :math:`\{ 0, 1, \ldots, n-1 \}`。
``Finset`` 还允许你通过枚举元素来定义有限集：
TEXT. -/
-- QUOTE:
#check ({0, 2, 5} : Finset Nat)

def example1 : Finset ℕ := {0, 1, 2}
-- QUOTE.

/- TEXT:
有多种方法让 Lean 认识到以这种方式呈现的集合中元素的顺序和
重复无关紧要。
EXAMPLES: -/
-- QUOTE:
example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide

example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp [or_comm, or_left_comm]

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp; tauto
-- QUOTE.

/- TEXT:
你可以使用 ``insert`` 向有限集添加单个元素，使用 ``Finset.erase``
删除单个元素。
请注意 ``erase`` 在 ``Finset`` 命名空间中，但 ``insert`` 在根命名空间中。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h
-- QUOTE.

/- TEXT:
实际上，``{0, 1, 2}`` 就是 ``insert 0 (insert 1 (singleton 2))`` 的记号。
EXAMPLES: -/
-- QUOTE:
set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)
-- QUOTE.

/- TEXT:
给定一个有限集 ``s`` 和一个谓词 ``P``，我们可以使用集合构造记号 ``{x ∈ s | P x}`` 来
定义 ``s`` 中满足 ``P`` 的元素组成的集合。
这是 ``Finset.filter P s`` 的记号，也可以写作 ``s.filter P``。
EXAMPLES: -/
-- QUOTE:
example : {m ∈ range n | Even m} = (range n).filter Even := rfl
example : {m ∈ range n | Even m ∧ m ≠ 3} = (range n).filter (fun m ↦ Even m ∧ m ≠ 3) := rfl

example : {m ∈ range 10 | Even m} = {0, 2, 4, 6, 8} := by decide
-- QUOTE.

/- TEXT:
Mathlib 知道函数下有限集的像是有限集。
EXAMPLES: -/
-- QUOTE:
#check (range 5).image (fun x ↦ x * 2)

example : (range 5).image (fun x ↦ x * 2) = {x ∈ range 10 | Even x} := by decide
-- QUOTE.

/- TEXT:
Lean 也知道两个有限集的笛卡尔积 ``s ×ˢ t`` 是有限集，
并且有限集的幂集是有限集。（请注意记号 ``s ×ˢ t``
也适用于集合。）
EXAMPLES: -/
section
variable (s t : Finset Nat)
-- QUOTE:
#check s ×ˢ t
#check s.powerset
-- QUOTE:

end

/- TEXT:
用有限集的元素来定义其上的操作是微妙的，因为任何这样的定义
都必须与元素呈现的顺序无关。
当然，你总是可以通过组合已有的操作来定义函数。
另一个你可以做的事情是使用 ``Finset.fold`` 在元素上折叠一个二元运算，
前提是该运算是结合且交换的，
因为这些性质保证了结果与运算应用的顺序无关。
有限和、积和并都是以这种方式定义的。
在下面最后一个例子中，``biUnion`` 代表"有界索引并"。
用传统的数学记号，该表达式将写作
:math:`\bigcup_{i ∈ s} g(i)`。
EXAMPLES: -/
namespace finsets_and_fintypes
-- QUOTE:
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g
-- QUOTE.

end finsets_and_fintypes

/- TEXT:
关于有限集有一个自然的归纳原理：要证明每个有限集
都具有某个性质，只需证明空集具有该性质，并且当我们
向有限集添加一个新元素时该性质得以保持。（下一个例子的归纳步骤中需要
``@insert`` 中的 ``@`` 符号来为参数 ``a`` 和 ``s`` 命名，
因为它们被标记为隐式的。）
EXAMPLES: -/
-- QUOTE:
#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s anins ih =>
    rw [prod_insert anins]
    apply mul_ne_zero
    · apply h; apply mem_insert_self
    apply ih
    intros x xs
    exact h x (mem_insert_of_mem xs)
-- QUOTE.

/- TEXT:
如果 ``s`` 是一个有限集，``Finset.Nonempty s`` 定义为 ``∃ x, x ∈ s``。
你可以使用经典选择来选取一个非空有限集的元素。类似地，
库定义了 ``Finset.toList s``，它使用选择以某种顺序选取
``s`` 的元素。
EXAMPLES: -/
-- QUOTE:
noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s := Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList
-- QUOTE.

/- TEXT:
你可以使用 ``Finset.min`` 和 ``Finset.max`` 来选取线性序有限集中元素的最小值或最大值，
类似地，你可以使用 ``Finset.inf``
和 ``Finset.sup`` 来处理格中元素的有限集，
但有一个陷阱。
空有限集的最小元素应该是什么？
你可以检查下面带撇号版本的函数添加了一个前提条件，
即有限集非空。
不带撇号的版本 ``Finset.min`` 和 ``Finset.max``
分别在输出类型中添加了顶元素或底元素，以处理
有限集为空的情况。
不带撇号的版本 ``Finset.inf`` 和 ``Finset.sup`` 假设
该格分别配备了顶元素或底元素。
EXAMPLES: -/
-- QUOTE:
#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial
-- QUOTE.

/- TEXT:
每个有限集 ``s`` 都有一个有限的基数，``Finset.card s``，当 ``Finset`` 命名空间打开时
可以写作 ``#s``。

EXAMPLES: -/
-- QUOTE:
#check Finset.card

#eval (range 5).card

example (s : Finset ℕ) : s.card = #s := by rfl

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by simp
-- QUOTE.

/- TEXT:
下一节全是关于基数推理的。

在形式化数学时，人们常常需要决定是否用集合还是类型
来表达自己的定义和定理。
使用类型通常可以简化记号和证明，
但处理类型的子集可以更灵活。
有限集的基于类型的类似物是*有限类型*，即对于某个 ``α``，
类型 ``Fintype α``。
根据定义，有限类型只是一个配备了包含其所有元素的
有限集 ``univ`` 的数据类型。
EXAMPLES: -/
section
-- QUOTE:
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x
-- QUOTE.

/- TEXT:
``Fintype.card α`` 等于相应有限集的基数。
EXAMPLES: -/
-- QUOTE:
example : Fintype.card α = (Finset.univ : Finset α).card := rfl
-- QUOTE.
end

/- TEXT:
我们已经见过一个有限类型的原型例子，即对每个 ``n``，
类型 ``Fin n``。
Lean 知道有限类型对诸如乘积运算等操作是封闭的。
EXAMPLES: -/
-- QUOTE:
example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp
-- QUOTE.

/- TEXT:
``Finset α`` 的任何元素 ``s`` 都可以被强制转换为类型 ``(↑s : Fintype α)``，
即包含在 ``s`` 中的 ``α`` 元素的子类型。
EXAMPLES: -/
section
-- QUOTE:
variable (s : Finset ℕ)

example : (↑s : Type) = {x : ℕ // x ∈ s} := rfl
example : Fintype.card ↑s = s.card := by simp
-- QUOTE.
end

/- TEXT:
Lean 和 Mathlib 使用*类型类推断*来跟踪有限类型上的附加结构，
即包含所有元素的通用有限集。
换句话说，你可以将有限类型视为配备了该额外数据的代数结构。
:numref:`Chapter %s <structures>` 解释了这是如何工作的。
EXAMPLES: -/
