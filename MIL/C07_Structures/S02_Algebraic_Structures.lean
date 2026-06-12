import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

/- TEXT:
.. _section_algebraic_structures:

代数结构
--------------------

为了澄清我们所说的*代数结构*这个短语的含义，
考虑一些例子会有所帮助。

#. *偏序集*由一个集合 :math:`P` 和 :math:`P` 上的一个二元关系 :math:`\le` 组成，
   该关系是传递的、自反的和反对称的。

#. *群*由一个集合 :math:`G` 以及一个结合的二元运算、一个单位元
   :math:`1`，以及一个函数 :math:`g \mapsto g^{-1}` 组成，该函数为
   :math:`G` 中的每个 :math:`g` 返回一个逆元。
   如果运算可交换，则称为*阿贝尔群*或*交换群*。

#. *格*是具有交和并的偏序集。

#. *环*由一个（加法书写的）阿贝尔群
   :math:`(R, +, 0, x \mapsto -x)`
   以及一个结合的乘法运算
   :math:`\cdot` 和一个单位元 :math:`1` 组成，
   满足乘法对加法分配。
   如果乘法可交换，则环是*交换的*。

#. *有序环* :math:`(R, +, 0, -, \cdot, 1, \le)` 由一个环
   以及其元素上的一个偏序组成，满足对 :math:`R` 中任意的 :math:`a`、:math:`b` 和 :math:`c`，
   若 :math:`a \le b` 则 :math:`a + c \le b + c`，
   且对 :math:`R` 中任意的 :math:`a` 和 :math:`b`，
   若 :math:`0 \le a` 且 :math:`0 \le b` 则 :math:`0 \le a b`。

#. *度量空间*由一个集合 :math:`X` 和一个函数
   :math:`d : X \times X \to \mathbb{R}` 组成，满足以下条件：

   - 对 :math:`X` 中任意的 :math:`x` 和 :math:`y`，:math:`d(x, y) \ge 0`。
   - :math:`d(x, y) = 0` 当且仅当 :math:`x = y`。
   - 对 :math:`X` 中任意的 :math:`x` 和 :math:`y`，:math:`d(x, y) = d(y, x)`。
   - 对 :math:`X` 中任意的 :math:`x`、:math:`y` 和 :math:`z`，
     :math:`d(x, z) \le d(x, y) + d(y, z)`。

#. *拓扑空间*由一个集合 :math:`X` 和 :math:`X` 的子集的集合 :math:`\mathcal T`
   组成，这些子集称为 :math:`X` 的*开子集*，满足以下条件：

   - 空集和 :math:`X` 是开集。
   - 两个开集的交是开集。
   - 任意多个开集的并是开集。

在这些例子的每一个中，结构的元素属于一个集合，
即*基集*，该集合有时代表整个结构。
例如，当我们说"设 :math:`G` 是一个群"然后
"设 :math:`g \in G`，"我们将 :math:`G` 用于代表
结构及其基集。
并不是每个代数结构都以这种方式与单个基集相关联。
例如，一个*二部图*涉及两个集合之间的关系，
*伽罗瓦连接*也是如此。
一个*范畴*也涉及两个感兴趣的集合，通常称为*对象*
和*态射*。

这些例子指出了证明助手为了支持代数推理
而必须做的一些事情。
首先，它需要识别结构的具体实例。
数系 :math:`\mathbb{Z}`、:math:`\mathbb{Q}`
和 :math:`\mathbb{R}` 都是有序环，
我们应该能够在任何这些实例中应用关于有序环的泛型定理。
有时一个具体的集合可能以不止一种方式成为一个结构的实例。
例如，除了 :math:`\mathbb{R}` 上构成实分析基础的通常拓扑外，
我们还可以考虑 :math:`\mathbb{R}` 上的*离散*拓扑，
其中每个集合都是开集。

其次，证明助手需要支持结构上的泛型记号。
在 Lean 中，记号 ``*``
用于所有通常数系中的乘法，
以及泛型群和环中的乘法。
当我们使用像 ``f x * y`` 这样的表达式时，
Lean 必须使用关于 ``f``、``x`` 和 ``y`` 的类型信息
来确定我们心中所想的乘法是哪一个。

第三，它需要处理结构可以以各种方式
从其他结构继承定义、定理和记号的事实。
一些结构通过添加更多公理来扩展其他结构。
交换环仍然是环，因此任何在环中有意义的定义
在交换环中也有意义，
且任何在环中成立的定理在交换环中也成立。
一些结构通过添加更多数据来扩展其他结构。
例如，任何环的加法部分都是一个加法群。
环结构添加了乘法和一个单位元，
以及控制它们并将其与加法部分联系起来的公理。
有时我们可以用另一个结构来定义一个结构。
任何度量空间都有一个与之关联的规范拓扑，
即*度量空间拓扑*，并且有各种可以与
任何线性序相关联的拓扑。

最后，重要的是要记住数学允许我们使用函数和运算
来定义结构，就像我们使用函数和运算来定义数字一样。
群的乘积和幂再次是群。
对每个 :math:`n`，模 :math:`n` 的整数构成一个环，
且对每个 :math:`k > 0`，系数在该环中的多项式的 :math:`k \times k` 矩阵
再次构成一个环。
因此，我们可以像计算结构的元素一样轻松地计算结构本身。
这意味着代数结构在数学中过着双重生活，
既作为对象集合的容器，又作为其自身的对象。
证明助手必须适应这种双重角色。

当处理具有与之关联的代数结构的
类型的元素时，
证明助手需要识别该结构并找到相关的
定义、定理和记号。
所有这些听起来应该像是大量的工作，而事实也确实如此。
但 Lean 使用一小组基本机制来
执行这些任务。
本节的目标是解释这些机制并向你展示
如何使用它们。

第一个要素几乎显而易见，以至于不需要提及：
从形式上讲，代数结构就是
:numref:`section_structures` 意义上的结构体。
代数结构是满足某些公理假设的数据束的规范说明，
我们在 :numref:`section_structures` 中看到
这正是 ``structure`` 命令被设计来容纳的。
这真是天作之合！

给定一个数据类型 ``α``，我们可以如下在 ``α`` 上定义一个群结构。
EXAMPLES: -/
-- QUOTE:
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
-- QUOTE.

-- OMIT: TODO: 稍后解释 extends 命令，以及冗余继承
/- TEXT:
请注意类型 ``α`` 是 ``Group₁`` 定义中的一个*参数*。
所以你应该将对象 ``struc : Group₁ α`` 视为
``α`` 上的一个群结构。
我们在 :numref:`proving_identities_in_algebraic_structures` 中看到
与 ``inv_mul_cancel`` 对应的 ``mul_inv_cancel``
可以从其他群公理推出，因此无需
将其添加到定义中。

这个群的定义类似于 Mathlib 中 ``Group`` 的定义，
我们选择了名称 ``Group₁`` 以区别于我们的版本。
如果你写 ``#check Group`` 并在定义上按 ctrl-click，
你会看到 Mathlib 中的 ``Group`` 被定义为扩展另一个结构体；
我们将在后面解释如何做到这一点。
如果你输入 ``#print Group``，你还会看到 Mathlib
中的 ``Group`` 有许多额外的字段。
由于我们稍后将解释的原因，有时向结构体添加
冗余信息是有用的，
这样就有额外的字段用于可以从核心数据
定义的对象和函数。
现在不用担心这个。
请放心，我们简化的版本 ``Group₁`` 在本质上
与 Mathlib 使用的群的定义是相同的。

有时将类型与结构体捆绑在一起是有用的，Mathlib 还
包含一个 ``Grp`` 结构的定义，它等价于
以下内容：
EXAMPLES: -/
-- QUOTE:
structure Grp₁ where
  α : Type*
  str : Group₁ α
-- QUOTE.

/- TEXT:
Mathlib 版本位于 ``Mathlib.Algebra.Category.Grp.Basic``，
如果你将它添加到示例文件开头的导入中，就可以
``#check`` 它。

由于下面将变得更清晰的原因，更常见的是
将类型 ``α`` 与结构 ``Group α`` 分开，
这更有用。
我们将这两个对象一起称为*部分打包的结构体*，
因为该表示将大部分（但不是全部）分量
组合到一个结构体中。在 Mathlib 中，
当类型被用作群的基类型时，
通常使用大写罗马字母如 ``G`` 来表示。

让我们构造一个群，也就是说，构造 ``Group₁`` 类型的一个元素。
对于任意一对类型 ``α`` 和 ``β``，Mathlib 定义了 ``α`` 和 ``β`` 之间
*等价关系*的类型 ``Equiv α β``。
Mathlib 还为该类型定义了提示性的记号 ``α ≃ β``。
一个元素 ``f : α ≃ β`` 是 ``α`` 和 ``β`` 之间的双射，
由四个分量表示：
从 ``α`` 到 ``β`` 的函数 ``f.toFun``，
从 ``β`` 到 ``α`` 的逆函数 ``f.invFun``，
以及两个指定这些函数确实互逆的性质。
EXAMPLES: -/
section
-- QUOTE:
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)
-- QUOTE.

/- TEXT:
请注意最后三个构造的创造性命名。我们将
恒等函数 ``Equiv.refl``、逆运算 ``Equiv.symm``
和复合运算 ``Equiv.trans`` 视为存在双射对应关系
这一性质是等价关系的显式证据。

还请注意 ``f.trans g`` 需要按逆序复合前向函数。
Mathlib 声明了一个从 ``Equiv α β``
到函数类型 ``α → β`` 的*强制转换*，因此我们可以省略写 ``.toFun``
而让 Lean 为我们插入它。
EXAMPLES: -/
-- QUOTE:
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl
-- QUOTE.

end

/- TEXT:
Mathlib 还定义了 ``α`` 与自身的等价关系的类型 ``Perm α``。
EXAMPLES: -/
-- QUOTE:
example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl
-- QUOTE.

/- TEXT:
很明显，``Equiv.Perm α`` 在等价关系的复合下构成一个群。
我们以这样的方式定向，使得 ``mul f g`` 等于 ``g.trans f``，
其前向函数是 ``f ∘ g``。
换句话说，乘法就是我们通常认为的
双射的复合。这里我们定义这个群：
EXAMPLES: -/
-- QUOTE:
def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc h g f).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- TEXT:
实际上，Mathlib 在文件 ``Algebra.Group.End`` 中正好在 ``Equiv.Perm α`` 上
定义了这个 ``Group`` 结构。
一如既往，你可以将鼠标悬停在 ``permGroup`` 的定义中所使用的定理上
来查看它们的陈述，
你也可以跳转到原始文件中它们的定义来了解更多
关于它们是如何实现的。

在通常的数学中，我们通常认为记号是
独立于结构的。
例如，我们可以考虑群 :math:`(G_1, \cdot, 1, \cdot^{-1})`、
:math:`(G_2, \circ, e, i(\cdot))` 和 :math:`(G_3, +, 0, -)`。
在第一种情况下，我们将二元运算写作 :math:`\cdot`，
单位元写作 :math:`1`，逆函数写作 :math:`x \mapsto x^{-1}`。
在第二和第三种情况下，我们使用所示的记号替代方案。
然而，当我们在 Lean 中形式化群的概念时，
记号更紧密地与结构相关联。
在 Lean 中，任何 ``Group`` 的分量被命名为
``mul``、``one`` 和 ``inv``，
稍后我们将看到乘法记号是
如何设置为引用它们的。
如果我们想使用加法记号，我们改为使用同构的结构体
``AddGroup``（加法群底层的结构体）。其分量命名为 ``add``、``zero``
和 ``neg``，关联的记号正如你所期望的那样。

回忆我们在 :numref:`section_structures` 中定义的类型 ``Point``，
以及我们在那里定义的加法函数。
这些定义在本节附带的示例文件中被重现。
作为练习，定义一个类似于我们上面定义的
``Group₁`` 结构体的 ``AddGroup₁`` 结构体，只是它使用刚才描述的
加法命名方案。
在 ``Point`` 数据类型上定义负元和一个零元，
并在 ``Point`` 上定义 ``AddGroup₁`` 结构体。
BOTH: -/
-- QUOTE:
structure AddGroup₁ (α : Type*) where
/- EXAMPLES:
  (add : α → α → α)
  -- 填写剩余部分
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

-- BOTH:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/- EXAMPLES:
def neg (a : Point) : Point := sorry

def zero : Point := sorry

def addGroupPoint : AddGroup₁ Point := sorry

SOLUTIONS: -/
def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

-- BOTH:
end Point
-- QUOTE.

/- TEXT:
我们正在取得进展。
现在我们知道如何在 Lean 中定义代数结构，
也知道如何定义这些结构的实例。
但我们也想将记号与结构关联起来，
以便我们可以对每个实例使用它。
此外，我们想安排它使得我们可以定义一个
结构上的运算并将其用于任何特定实例，
并且我们想安排它使得我们可以证明一个关于
结构的定理并将其用于任何实例。

实际上，Mathlib 已经设置为对 ``Equiv.Perm α`` 使用泛型群记号、
定义和定理。
EXAMPLES: -/
section
-- QUOTE:
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- 群幂，对任何群定义
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g
-- QUOTE.

end

/- TEXT:
你可以检查，对于我们上面要求你在 ``Point`` 上定义的加法群结构，
情况并非如此。
我们现在的任务是理解在幕后发生的魔法，
以使 ``Equiv.Perm α`` 的例子按它们的方式工作。

问题在于 Lean 需要能够使用我们在
输入的表达式中所找到的信息来*找到*相关的记号和隐含的群结构。
类似地，当我们用类型为 ``ℝ`` 的表达式 ``x`` 和 ``y`` 写出 ``x + y`` 时，
Lean 需要将 ``+`` 符号解释为实数上的相关加法函数。
它还必须认出类型 ``ℝ`` 是交换环的一个实例，
以便交换环的所有定义和定理都可用。
另一个例子，
连续性在 Lean 中是相对于任意两个拓扑空间定义的。
当我们有 ``f : ℝ → ℂ`` 并写 ``Continuous f`` 时，Lean 必须找到
``ℝ`` 和 ``ℂ`` 上的相关拓扑。

这个魔法是通过三样东西的组合实现的。

#. *逻辑。* 一个应该在任意群中解释的定义，
   将群的类型和群结构作为参数。
   类似地，一个关于任意群的元素的定理
   以关于群的类型和群结构的
   全称量词开始。

#. *隐式参数。* 类型和结构的参数
   通常保持隐式，这样我们就不必写它们
   或在 Lean 信息窗口中看到它们。Lean 默默地
   为我们填写信息。

#. *类型类推断。* 也称为*类推断*，
   这是一个简单但强大的机制，
   使我们能够注册信息以供 Lean 以后使用。
   当 Lean 被要求填写定义、定理或记号的
   隐式参数时，
   它可以使用已注册的信息。

注解 ``(grp : Group G)`` 告诉 Lean 它应该
期望被显式地给定该参数，注解
``{grp : Group G}`` 告诉 Lean 它应该尝试从表达式中的
上下文线索来推断它，
而注解 ``[grp : Group G]`` 告诉 Lean 相应的
参数应该使用类型类推断来合成。
由于使用此类参数的全部意义在于
我们通常不需要显式地引用它们，
Lean 允许我们写 ``[Group G]`` 并将名称保持为匿名。
你可能已经注意到 Lean 自动选择像 ``_inst_1`` 这样的
名称。
当我们将匿名方括号注解与 ``variable`` 命令一起使用时，
那么只要变量仍然在作用域内，
Lean 自动将参数 ``[Group G]`` 添加到任何提及 ``G`` 的定义或
定理中。

我们如何注册 Lean 用于执行搜索
所需的信息？
回到我们的群例子，我们只需要做两个更改。
首先，不使用 ``structure`` 命令来定义群结构，
我们使用关键字 ``class`` 来指示它是
类推断的候选。
其次，不使用 ``def`` 定义特定实例，
我们使用关键字 ``instance`` 向 Lean 注册特定实例。
与类变量的名称一样，我们允许将
实例定义的名称保持匿名，
因为一般来说我们打算让 Lean 找到它并使用它，
而不用细节来困扰我们。
EXAMPLES: -/
-- QUOTE:
class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc h g f).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- TEXT:
以下示例说明了它们的用法。
EXAMPLES: -/
-- QUOTE:
#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end
-- QUOTE.

/- TEXT:
``#check`` 命令显示 ``Group₂.mul`` 有一个隐式参数
``[Group₂ α]``，我们期望通过类推断找到它，
其中 ``α`` 是 ``Group₂.mul`` 的参数的类型。
换句话说，``{α : Type*}`` 是群元素类型的隐式参数，
``[Group₂ α]`` 是 ``α`` 上群结构的隐式参数。
类似地，当我们为 ``Group₂`` 定义一个泛型平方函数 ``my_square`` 时，
我们使用隐式参数 ``{α : Type*}`` 表示元素类型，
并使用隐式参数 ``[Group₂ α]`` 表示
``Group₂`` 结构。

在第一个例子中，
当我们写 ``Group₂.mul f g`` 时，``f`` 和 ``g`` 的类型
告诉 Lean ``Group₂.mul`` 中参数 ``α``
必须实例化为 ``Equiv.Perm β``。
这意味着 Lean 必须找到 ``Group₂ (Equiv.Perm β)`` 的一个元素。
前面的 ``instance`` 声明正好告诉 Lean 如何做到这一点。
问题解决了！

这种为了在 Lean 需要时找到信息而注册信息
的简单机制非常有用。
这里有一种它的应用方式。
在 Lean 的基础中，数据类型 ``α`` 可能为空。
然而，在许多应用中，知道一个类型至少有一个元素
是有用的。
例如，函数 ``List.headI`` 返回列表的第一个元素，
当列表为空时可以返回默认值。
为了实现这一点，Lean 库定义了一个类 ``Inhabited α``，
它仅仅存储一个默认值。
我们可以证明 ``Point`` 类型是一个实例：
EXAMPLES: -/
-- QUOTE:
instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl
-- QUOTE.

/- TEXT:
类推断机制也用于泛型记号。
表达式 ``x + y`` 是 ``Add.add x y`` 的缩写，
其中——你猜对了——``Add α`` 是一个存储
``α`` 上一个二元函数的类。
写 ``x + y`` 告诉 Lean 找到一个已注册的 ``[Add.add α]`` 实例
并使用相应的函数。
下面，我们为 ``Point`` 注册加法函数。
EXAMPLES: -/
-- QUOTE:
instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end
-- QUOTE.

/- TEXT:
这样，我们也可以将记号 ``+`` 分配给其他类型的二元运算。

但我们还可以做得更好。我们已经看到 ``*`` 可以在任何群中使用，
``+`` 可以在任何加法群中使用，两者都可以在任何环中使用。
当我们在 Lean 中定义环的新实例时，
我们不必为该实例定义 ``+`` 和 ``*``，
因为 Lean 知道这些对每个环都是已定义的。
我们可以使用这种方法为我们的 ``Group₂`` 类指定记号：
EXAMPLES: -/
-- QUOTE:
instance {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
-- QUOTE.

/- TEXT:
使这种方法有效的原因是 Lean 执行递归搜索。
根据我们已声明的实例，Lean 可以通过找到
一个 ``Group₂ (Equiv.Perm α)`` 的实例来找到 ``Mul (Equiv.Perm α)`` 的实例，
而它可以找到 ``Group₂ (Equiv.Perm α)`` 的实例，因为我们提供了它。
Lean 能够找到这两个事实并将它们链接在一起。

我们刚刚给出的例子是危险的，因为 Lean 的
库中也有一个 ``Group (Equiv.Perm α)`` 的实例，并且
乘法是在任何群上定义的。
因此关于找到哪个实例是不明确的。
实际上，除非你显式指定不同的优先级，Lean 更倾向于最近声明的实例。
另外，还有另一种方法告诉 Lean 一个结构体是另一个结构体的
实例，使用 ``extends`` 关键字。
这就是 Mathlib 指定例如每个交换环
都是环的方式。
你可以在 :numref:`hierarchies` 和 *Theorem Proving in Lean* 中关于
`类推断的章节 <https://leanprover.github.io/theorem_proving_in_lean4/Type-Classes/#managing-type-class-inference>`_ 找到更多信息。

一般来说，为已经定义了记号的
代数结构的实例指定 ``*`` 的值
是一个坏主意。
在 Lean 中重新定义 ``Group`` 的概念是一个人为的例子。
然而，在这种情况下，两种对群记号的解释都以相同的方式展开为
``Equiv.trans``、``Equiv.refl`` 和 ``Equiv.symm``。

作为一个类似的人为练习，
在 ``Group₂`` 的类比中定义一个类 ``AddGroup₂``。
对任何 ``AddGroup₂`` 使用 ``Add``、``Neg`` 和 ``Zero`` 类
定义通常的加法、负元和零的记号。
然后证明 ``Point`` 是 ``AddGroup₂`` 的一个实例。
试试看，确保加法群记号对
``Point`` 的元素有效。
BOTH: -/
-- QUOTE:
class AddGroup₂ (α : Type*) where
/- EXAMPLES:
  add : α → α → α
  -- 填写剩余部分
-- QUOTE.
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α :=
  ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α :=
  ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α :=
  ⟨AddGroup₂.neg⟩

instance : AddGroup₂ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

section
variable (x y : Point)

#check x + -y + 0

end

/- TEXT:
我们已经在上面对 ``Point`` 声明了 ``Add``、``Neg`` 和 ``Zero`` 的实例，
这不算什么大问题。
再次，两种合成记号的方式应该得出相同的答案。

类推断是微妙的，你在使用时必须小心，
因为它配置了自动化，无形地支配着我们输入的
表达式的解释。
然而，当明智地使用时，类推断是一个强大的工具。
它使得在 Lean 中进行代数推理成为可能。
TEXT. -/
