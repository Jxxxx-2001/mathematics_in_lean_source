import MIL.Common
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

/- TEXT:
.. _section_structures:

定义结构体
-------------------

在最广泛的意义上，*结构体*是数据集合的规范说明，
可能带有数据需要满足的约束条件。
结构体的*实例*是满足约束条件的特定数据束。
例如，我们可以指定一个点为三个实数的元组：
BOTH: -/
-- QUOTE:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
-- QUOTE.

/- TEXT:
``@[ext]`` 注解告诉 Lean 自动生成
可用于证明结构体的两个实例在分量相等时相等
的定理，这个性质被称为*外延性*。
EXAMPLES: -/
-- QUOTE:
#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption
-- QUOTE.

/- TEXT:
然后我们可以定义 ``Point`` 结构体的特定实例。
Lean 提供了多种方法来实现这一点。
EXAMPLES: -/
-- QUOTE:
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  { x := 2, y := -1, z := 4 }

def myPoint3 : Point :=
  ⟨2, -1, 4⟩

def myPoint4 :=
  Point.mk 2 (-1) 4
-- QUOTE.

/- TEXT:
..
  因为 Lean 知道 ``myPoint1`` 的期望类型是 ``Point``，
  你可以通过写下划线 ``_`` 来开始定义。
  点击 VS Code 中附近出现的灯泡
  然后会给你一个选项，插入一个模板定义，
  其中为你列出了字段名。

在第一个例子中，结构体的字段被显式
命名。
在 ``myPoint4`` 的定义中提到的函数 ``Point.mk``
被称为 ``Point`` 结构体的*构造子*，因为
它用于构造元素。
如果你愿意，可以指定不同的名称，比如 ``build``。
EXAMPLES: -/
-- QUOTE:
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4
-- QUOTE.

/- TEXT:
接下来的两个例子展示了如何在结构体上定义函数。
第二个例子显式使用了 ``Point.mk``
构造子，而第一个例子为了简洁使用了匿名构造子。
Lean 可以从 ``add`` 的指定类型推断出
相关的构造子。
通常的做法是将与像 ``Point`` 这样的结构体相关联的
定义和定理放在同名的命名空间中。
在下面的例子中，因为我们打开了 ``Point``
命名空间，``add`` 的全名是 ``Point.add``。
当命名空间未打开时，我们必须使用全名。
但请记住，使用匿名投影记号通常很方便，
它允许我们写 ``a.add b`` 而不是 ``Point.add a b``。
Lean 将前者解释为后者，因为 ``a`` 的类型是 ``Point``。
BOTH: -/
-- QUOTE:
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

-- EXAMPLES:
def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2
-- QUOTE.

/- TEXT:
下面我们将继续把定义放在相关的
命名空间中，但我们会在引用的代码片段中省略命名空间命令。
要证明加法函数的性质，
我们可以使用 ``rw`` 展开定义，并使用 ``ext`` 将
结构体两个元素之间的等式归结为分量之间
的等式。
下面我们使用 ``protected`` 关键字，这样即使在命名空间打开时，
定理的名称仍然是 ``Point.add_comm``。
这在我们希望避免与像 ``add_comm`` 这样的泛型
定理产生歧义时很有帮助。
EXAMPLES: -/
namespace Point

-- QUOTE:
protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
-- QUOTE.

/- TEXT:
因为 Lean 可以内部展开定义并简化投影，
有时我们想要的等式按定义成立。
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl
-- QUOTE.

/- TEXT:
也可以使用模式匹配来定义结构体上的函数，
这类似于我们在
:numref:`section_induction_and_recursion` 中定义递归函数的方法。
下面的 ``addAlt`` 和 ``addAlt'`` 的定义本质上是相同的；
唯一的区别是我们在第二个中使用了匿名构造子记号。
虽然有时以这种方式定义函数很方便，而且结构 eta-归约使这个
替代方案在定义上等价，但它可能使后续的证明变得不太方便。
特别是，``rw [addAlt]`` 给我们留下了一个包含 ``match`` 语句的
更混乱的目标视图。
EXAMPLES: -/
-- QUOTE:
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- 同样的证明仍然有效，但这里的目标视图更难阅读
  ext <;> dsimp
  repeat' apply add_comm
-- QUOTE.

/- TEXT:
数学构造通常涉及将打包的信息拆开并以不同的方式重新组合。
因此，Lean 和 Mathlib 提供如此多的高效完成此操作的方法
是合理的。
作为练习，尝试证明 ``Point.add`` 是结合的。
然后为点定义标量乘法并证明它
对加法分配。
BOTH: -/
-- QUOTE:
protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, add_assoc]
-- BOTH:

def smul (r : ℝ) (a : Point) : Point :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ⟨r * a.x, r * a.y, r * a.z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, smul, mul_add]
-- BOTH:
-- QUOTE.

end Point

/- TEXT:
使用结构体只是通向代数抽象道路上的第一步。
我们还没有办法将 ``Point.add`` 与泛型 ``+`` 符号联系起来，
也没有办法将 ``Point.add_comm`` 和 ``Point.add_assoc`` 与
泛型 ``add_comm`` 和 ``add_assoc`` 定理联系起来。
这些任务属于使用结构体的*代数*方面，
我们将在下一节解释如何完成它们。
现在，只需将结构体视为一种将对象和信息捆绑在一起的方式。

特别有用的是，结构体不仅可以指定
数据类型，还可以指定数据必须满足的约束条件。
在 Lean 中，后者表示为类型为 ``Prop`` 的字段。
例如，*标准 2-单形* 定义为满足 :math:`x ≥ 0`、:math:`y ≥ 0`、:math:`z ≥ 0`
和 :math:`x + y + z = 1` 的点 :math:`(x, y, z)` 的集合。
如果你不熟悉这个概念，你应该画个图，
并说服自己这个集合是
三维空间中具有顶点
:math:`(1, 0, 0)`、:math:`(0, 1, 0)` 和 :math:`(0, 0, 1)` 的等边三角形
及其内部。
我们可以在 Lean 中如下表示它：
BOTH: -/
-- QUOTE:
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1
-- QUOTE.

/- TEXT:
请注意最后四个字段引用了 ``x``、``y`` 和 ``z``，
即前三个字段。
我们可以定义一个从二单形到自身的映射，交换 ``x`` 和 ``y``：
BOTH: -/
namespace StandardTwoSimplex

-- EXAMPLES:
-- QUOTE:
def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]
-- QUOTE.

-- OMIT: (TODO) 当我们有对 noncomputable section 的良好解释时添加一个链接。
/- TEXT:
更有趣的是，我们可以计算单形上两个点的中点。
我们在本文件的开头添加了 ``noncomputable section``
短语，以便在实数上使用除法。
BOTH: -/
-- QUOTE:
noncomputable section

-- EXAMPLES:
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]
-- QUOTE.

/- TEXT:
这里我们使用了简洁的证明项建立了 ``x_nonneg``、``y_nonneg`` 和 ``z_nonneg``，
但使用 ``by`` 以策略模式建立了 ``sum_eq``。

给定一个满足 :math:`0 \le \lambda \le 1` 的参数 :math:`\lambda`，
我们可以取标准 2-单形中两点 :math:`a` 和 :math:`b` 的
加权平均 :math:`\lambda a + (1 - \lambda) b`。
我们挑战你定义这个函数，类似于上面的 ``midpoint``
函数。
BOTH: -/
-- QUOTE:
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
/- EXAMPLES:
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  sorry
SOLUTIONS: -/
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)
  sum_eq := by
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    · ring
    simp [a.sum_eq, b.sum_eq]
-- QUOTE.
-- BOTH:

end

end StandardTwoSimplex

/- TEXT:
结构体可以依赖于参数。
例如，我们可以将标准 2-单形推广到任意 :math:`n` 的
标准 :math:`n`-单形。
在此阶段，你不需要了解类型 ``Fin n`` 的任何信息，
除了它有 :math:`n` 个元素，并且 Lean 知道
如何对其求和。
BOTH: -/
-- QUOTE:
open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    norm_num

end StandardSimplex
-- QUOTE.

/- TEXT:
作为练习，看看你能否定义
标准 :math:`n`-单形中两点的加权平均。
你可以使用 ``Finset.sum_add_distrib``
和 ``Finset.mul_sum`` 来操作相关的和。

SOLUTIONS: -/
namespace StandardSimplex

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := lambda * a.V i + (1 - lambda) * b.V i
  NonNeg i :=
    add_nonneg (mul_nonneg lambda_nonneg (a.NonNeg i)) (mul_nonneg (by linarith) (b.NonNeg i))
  sum_eq_one := by
    trans (lambda * ∑ i, a.V i) + (1 - lambda) * ∑ i, b.V i
    · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp [a.sum_eq_one, b.sum_eq_one]

end StandardSimplex

/- TEXT:
我们已经看到结构体可以用于捆绑数据
和性质。
有趣的是，它们也可以用于捆绑性质
而不包含数据。
例如，下一个结构体 ``IsLinear`` 捆绑了
线性的两个组成部分。
EXAMPLES: -/
-- QUOTE:
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
-- QUOTE.

/- TEXT:
值得指出的是，结构体并不是捆绑数据的唯一方式。
``Point`` 数据结构可以使用泛型类型乘积来定义，
``IsLinear`` 可以用简单的 ``and`` 来定义。
EXAMPLES: -/
-- QUOTE:
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x
-- QUOTE.

/- TEXT:
泛型类型构造甚至可以用来代替分量之间
存在依赖关系的结构体。
例如，*子类型*构造将一段数据与
一个性质组合在一起。
你可以将下一个例子中的类型 ``PReal`` 视为
正实数的类型。
任何 ``x : PReal`` 有两个分量：值，以及为正的性质。
你可以将这些分量访问为 ``x.val``（类型为 ``ℝ``）
和 ``x.property``（表示 ``0 < x.val`` 的事实）。
EXAMPLES: -/
-- QUOTE:
def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end
-- QUOTE.

/- TEXT:
我们本可以使用子类型来定义标准 2-单形，
以及任意 :math:`n` 的标准 :math:`n`-单形。
EXAMPLES: -/
-- QUOTE:
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }
-- QUOTE.

/- TEXT:
类似地，*Sigma 类型*是有序对的推广，
其中第二个分量的类型依赖于第一个分量的类型。
EXAMPLES: -/
-- QUOTE:
def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
-- QUOTE.

/- TEXT:
给定 ``s : StdSimplex``，第一个分量 ``s.fst`` 是一个自然数，
第二个分量是相应的单形 ``StandardSimplex s.fst`` 的一个元素。
Sigma 类型和子类型的区别在于
Sigma 类型的第二个分量是数据而不是命题。

但即便我们可以使用乘积、子类型和 Sigma 类型
来代替结构体，使用结构体有许多优点。
定义结构体抽象了底层表示，
并为访问分量的函数提供了自定义名称。
这使得证明更健壮：
只依赖结构体接口的证明
在我们改变定义时通常仍然有效，
只要我们根据新定义重新定义旧的访问器。
此外，正如我们即将看到的，Lean 提供了对
将结构体编织成丰富、互联的层次结构，
以及管理它们之间交互的支持。
TEXT. -/
/- OMIT: (TODO)
来自 Patrick 的评论：
我们可以通过展示如何用 def point'' := ℝ × ℝ × ℝ 来访问点的分量，使这段内容不那么抽象。
然而，如果我们这样做，可能也应该诚实地提一下使用 fin 3 → ℝ 作为定义的可能性。
这无论如何都很有趣，因为我认为很少有数学家认识到将 ℝ^n 定义为迭代笛卡尔积
是一个礼貌的谎言，如果认真对待将是一场噩梦。

顺便说一下，我们是否应该包含一些关于与面向对象编程的相似性和差异的评论？
该页面的所有例子显然都很适合用 Python 中的类来实现。
而且我们迟早要面对 Lean 中的类和 C++ 或 Python 中的类之间的命名冲突。
如果 Lean 中的类能使用另一个名字，生活将会简单得多……
OMIT. -/
