-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

向量空间与线性映射
-----------------------------

向量空间
^^^^^^^^^^^^^

.. index:: vector space

我们将直接开始抽象线性代数，讨论任意域上的向量空间。
不过你可以在 :numref:`Section %s <matrices>` 中找到关于矩阵的内容，
该部分在逻辑上不依赖于这些抽象理论。
Mathlib 实际上处理的是涉及"模"这个词的更一般的线性代数版本，
但现在我们可以假装这只是拼写习惯上的古怪之处。

表示"设 :math:`K` 是一个域，且设 :math:`V` 是 :math:`K` 上的向量空间"
（并使它们成为后续结果的隐式参数）的方式是：

EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- TEXT:
我们在 :numref:`Chapter %s <hierarchies>` 中解释了为什么需要两个独立的
类型类 ``[AddCommGroup V] [Module K V]``。
简要说明如下。
从数学上讲，我们希望表达拥有 :math:`K`-向量空间结构
蕴含拥有加法交换群结构。
我们可以将这一点告诉 Lean。但这样一来，每当 Lean 需要在一个类型 :math:`V` 上寻找这样的
群结构时，它就会去搜索使用一个*完全未指定*的域 :math:`K` 的向量空间结构，
而这个 :math:`K` 无法从 :math:`V` 推导出来。
这对类型类综合系统将是非常不利的。

向量 `v` 与标量 `a` 的乘法记为
`a • v`。我们在以下示例中列出了关于此运算与加法相互作用的几条代数规则。
当然，`simp` 或 `apply?` 也可以找出这些证明。还有一个 `module` 策略，
它可以解决由向量空间和域的公理得出的目标，类似于在交换环中使用
`ring` 策略或在群中使用 `group` 策略。但记住标量乘法
在引理名称中缩写为 `smul` 仍然是有用的。


EXAMPLES: -/

-- QUOTE:
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- QUOTE.
/- TEXT:
作为给更高级读者的一条简要注释，让我们指出，正如术语所暗示的那样，
Mathlib 的线性代数也涵盖了（不一定交换的）环上的模。
事实上，它甚至涵盖了半环上的半模。如果你认为自己不需要
这种程度的普遍性，你可以思考以下示例，它很好地捕捉了
关于理想作用于子模的大量代数规则：
EXAMPLES: -/
-- QUOTE:
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module (Ideal R) (Submodule R M) :=
  inferInstance


-- QUOTE.
/- TEXT:
线性映射
^^^^^^^^^^^

.. index:: linear map

接下来我们需要线性映射。与群态射一样，Mathlib 中的线性映射是打包映射，
即由映射及其线性性质的证明组成的包。
这些打包映射在应用时会被转换为普通函数。
关于此设计的更多信息，请参见 :numref:`Chapter %s <hierarchies>`。

两个 ``K``-向量空间 ``V`` 和 ``W`` 之间的线性映射类型
记为 ``V →ₗ[K] W``。下标 `l` 表示线性（linear）。
起初在此记号中指定 ``K`` 可能显得有些奇怪。
但当多个域同时出现时，这一点至关重要。
例如，从 :math:`ℂ` 到 :math:`ℂ` 的实线性映射是形如 :math:`z ↦ az + b\bar{z}` 的所有映射，
而只有形如 :math:`z ↦ az` 的映射是复线性的，这一区别在复分析中至关重要。

EXAMPLES: -/
-- QUOTE:

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- QUOTE.

/- TEXT:
注意，``V →ₗ[K] W`` 本身带有有趣的代数结构（这是
打包这些映射的动机之一）。
它是一个 ``K``-向量空间，因此我们可以将线性映射相加并乘以标量。

EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- TEXT:
使用打包映射的一个缺点是，我们不能使用普通的函数复合。
我们需要使用 ``LinearMap.comp`` 或记号 ``∘ₗ``。

EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- TEXT:
构造线性映射主要有两种方式。
首先，我们可以通过提供函数和线性性证明来构建结构体。
像往常一样，这可以通过结构体代码操作来简化：你可以输入
``example : V →ₗ[K] V := _`` 并使用附加在下划线上的代码操作"Generate a skeleton"。
EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- TEXT:
你可能会好奇为什么 ``LinearMap`` 的证明字段名称以撇号结尾。
这是因为它们是在定义到函数的强制转换之前定义的，因此它们
用 ``LinearMap.toFun`` 来表述。然后它们被重新表述为 ``LinearMap.map_add``
和 ``LinearMap.map_smul``，使用到函数的强制转换。
这还不是故事的终点。人们还希望有一个适用于任何（打包的）保持加法的映射的 ``map_add`` 版本，
例如加法群态射、线性映射、连续线性映射、``K``-代数映射等。这就是 ``map_add``（在根命名空间中）。
中间版本 ``LinearMap.map_add`` 有些多余，但它允许使用点记号，
有时会很方便。``map_smul`` 也有类似的故事，一般框架
在 :numref:`Chapter %s <hierarchies>` 中有解释。
EXAMPLES: -/
-- QUOTE:

#check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
#check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
#check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

-- QUOTE.

/- TEXT:
也可以使用 Mathlib 中已经定义的各种组合子来构造线性映射。
例如，上面的例子已经被命名为 ``LinearMap.lsmul K V 3``。
``K`` 和 ``V`` 在这里是显式参数有几个原因。
最迫切的原因是，仅凭一个裸的 ``LinearMap.lsmul 3``，Lean 无法
推断出 ``V`` 甚至 ``K``。
但 ``LinearMap.lsmul K V`` 本身也是一个有趣的对象：它的类型是
``K →ₗ[K] V →ₗ[K] V``，这意味着它是从 ``K``
（视为自身上的向量空间）到从 ``V`` 到 ``V`` 的 ``K``-线性映射空间的 ``K``-线性映射。
EXAMPLES: -/
-- QUOTE:

#check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

-- QUOTE.

/- TEXT:
还有一个线性同构的类型 ``LinearEquiv``，记为 ``V ≃ₗ[K] W``。
``f : V ≃ₗ[K] W`` 的逆是 ``f.symm : W ≃ₗ[K] V``，
``f`` 和 ``g`` 的复合是 ``f.trans g``，也记为 ``f ≪≫ₗ g``，且
``V`` 的恒等同构是 ``LinearEquiv.refl K V``。
此类型的元素在需要时会自动强制转换为态射和函数。
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
可以使用 ``LinearEquiv.ofBijective`` 从双射态射构造同构。
这样做会使逆函数不可计算。
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.

/- TEXT:
注意，在上面的例子中，Lean 使用声明的类型来理解 ``.ofBijective``
指的是 ``LinearEquiv.ofBijective``（无需打开任何命名空间）。

向量空间的直和与直积
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

我们可以使用直和与直积从已有的向量空间构造新的向量空间。
让我们从两个向量空间开始。在这种情况下，直和与直积没有区别，
我们可以简单地使用积类型。
在下面的代码片段中，我们只是展示如何将所有结构映射（包含映射
和投影映射）作为线性映射获取，以及构造进入直积和从直和出发的线性映射的泛性质
（如果你不熟悉范畴论中直和与直积的区别，可以忽略泛性质这一术语，
只关注下面示例的类型）。
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- 第一投影映射
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- 第二投影映射
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- 直积的泛性质
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- 积映射按预期工作，第一分量
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- 积映射按预期工作，第二分量
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- 我们也可以并行地组合映射
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- 这只需通过将投影映射与泛性质相结合即可完成
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

-- 第一包含映射
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- 第二包含映射
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- 直和（也称为余积）的泛性质
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- 余积映射按预期工作，第一分量
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- 余积映射按预期工作，第二分量
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ

-- 余积映射以预期的方式定义
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
    φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl

end binary_product

-- QUOTE.
/- TEXT:
现在让我们转向任意族向量空间的直和与直积。
这里我们只需看看如何定义一族向量空间，以及如何获取直和与直积的泛性质。
注意，直和记号的作用域在 ``DirectSum`` 命名空间中，且
直和的泛性质要求指标类型上具有可判定的相等性
（这在某种程度上是实现的偶然结果）。
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

-- 直和的泛性质将来自各个直和项映射组合起来，构造出
-- 从直和出发的映射
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

-- 直积的泛性质将进入各个因子的映射组合起来，
-- 构造出进入直积的映射
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

-- 从直积出发的投影映射
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

-- 进入直和的包含映射
example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

-- 进入直积的包含映射
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

-- 如果 `ι` 是有限类型，则直和与直积之间存在一个同构。
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.
