import Mathlib

universe u v

open CategoryTheory

/-!
# 范畴论

lftcm2023 修改
-/

structure FlatCat where
  Obj : Type u
  Mor : Type v
  dom : Mor → Obj
  cod : Mor → Obj
  id : Obj → Mor
  id_dom (X : Obj) : dom (id X) = X
  id_cod (X : Obj) : cod (id X) = X
  com {f g : Mor} (h: cod f = dom g) : Mor
  com_dom {f g : Mor} (h: cod f = dom g) : dom (com h) = dom f
  com_cod {f g : Mor} (h: cod f = dom g) : cod (com h) = cod g
  -- ...

/-! 但这里使用 -/
structure NonFlatCat where
  Obj : Type u
  Mor : Obj → Obj → Type v
  id : (X : Obj) → Mor X X
  comp : (X Y Z :Obj) → (Mor X Y) → (Mor Y Z) → (Mor X Z)
  -- ...

/-!
## 基本概念

### 范畴、函子
-/

open Category CategoryTheory Limits

section

variable {C : Type} [Category C] {W X Y Z : C}

#check Category
#check _ ≅ _
#check Functor
#check NatTrans
#check _ ≌ _
#check Functor.category

example (l : Z ⟶ W) (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (g' : W ⟶ Y) (e : f ≫ g = g') :
    l ≫ f ≫ g ≫ h = (l ≫ g') ≫ h := by cat_disch

example (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 Y ≫ g = f ≫ g := by cat_disch

example {X : C} : C ⥤ Type where
  obj := fun Y => X ⟶ Y
  map f := ↾fun g => g ≫ f

#check Bicategory
#check Cat.bicategory
#check SmallCategory
#check LargeCategory
#check MorphismProperty.HasLocalization

/-
### 极限
-/
universe v' u'

#check IsLimit  -- 注意这并不是一个命题
#check HasLimit
#check limit
#check HasLimitsOfShape
#check HasLimitsOfSize

#check Cone.isLimitEquivIsTerminal
#check hasLimitsOfShape_iff_isLeftAdjoint_const

/-
让我们看一些例子。
-/
#check HasBinaryProduct
#check HasBinaryProducts
#check HasKernel
#check HasCokernel
#check HasKernels
#check HasCokernels
#check kernel
#check cokernel
#check kernel.ι
#check cokernel.π

/-
### Yoneda 引理
-/

#check yoneda
#check Yoneda.yoneda_full
#check Yoneda.yoneda_faithful
#check yonedaLemma

/-
## 更多内容
-/

#check Adjunction
#check MonoidalCategory
#check EnrichedCategory

#check Abelian
#check IsTriangulated
#check Functor.IsLocalization
#check DerivedCategory

#check GrothendieckTopology
#check Sheaf
#check Condensed

/-!
### 范畴的实例
-/

#check GrpCat                    -- 群
#check CommRingCat               -- 交换环
#check ModuleCat                 -- R-模
#check TopCat                    -- 拓扑空间
#check Rep                       -- k-线性 G-表示
#check AlgebraicGeometry.Scheme  -- 概形

#check ConcreteCategory

/-
## 练习

### 练习 1：Yoneda 嵌入
-/

section

open Opposite

variable (C : Type u) [Category.{v} C]

noncomputable def isoOfHomIso {X Y : C} (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
  yoneda.preimageIso h

end

/-
### 练习 2：环上的多项式构成一个函子
-/
section

noncomputable def RingCat.Polynomial : RingCat ⥤ RingCat where
  obj R := .of (_root_.Polynomial R)
  map f := RingCat.ofHom (_root_.Polynomial.mapRingHom f.hom)

end

/-
### 练习 3：等价与单态射
-/
section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

theorem equiv_reflects_monos {X Y : C} (f : X ⟶ Y) (e : C ≌ D) (hef : Mono (e.functor.map f)) :
    Mono f := (Functor.mono_map_iff_mono e.functor f).mp hef

end

/-
### 练习 4：可表函子
-/
section

open Polynomial

#check Polynomial.eval₂
#check Polynomial.eval₂RingHom

theorem CommRing.forget_representable : Functor.IsCorepresentable (forget CommRingCat.{0}) :=
  Functor.CorepresentableBy.isCorepresentable (X := .of ℤ[X])
    { homEquiv := fun {Y} =>
        { toFun f := f X
          invFun y := CommRingCat.ofHom (eval₂RingHom (Int.castRingHom Y) y)
          left_inv f := by ext1; exact ringHom_ext' (Subsingleton.elim _ _) (by simp)
          right_inv _ := by simp only [ConcreteCategory.hom_ofHom, coe_eval₂RingHom, eval₂_X] }
      homEquiv_comp _ _ := rfl }

#check CategoryTheory.Adjunction.corepresentableBy
#check CommRingCat.adj

theorem CommRing.forget_representable' : Functor.IsCorepresentable (forget CommRingCat.{0}) :=
  ((CommRingCat.adj.corepresentableBy PUnit.{1}).ofIso
    (Functor.isoWhiskerLeft (forget CommRingCat.{0}) Coyoneda.punitIso ≪≫
      (forget CommRingCat.{0}).rightUnitor)).isCorepresentable

end

/-
### 练习 6：推出与满态射

设 C 是一个范畴，X 和 Y 是对象，f : X ⟶ Y 是一个态射。证明 f 是满态射
当且仅当图表

X --f--→ Y
|        |
f        𝟙
|        |
↓        ↓
Y --𝟙--→ Y

是一个推出。
-/
section

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

def pushoutOfEpi {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  PushoutCocone.isColimitMkIdId f

end

/-
## 短复形与同调数据

同调库将可复合对

```
X₁ --f--> X₂ --g--> X₃
```

打包为单个对象：所有同调信息都成为附加在 `ShortComplex C` 的一个对象上的结构。
-/

section ShortComplexes

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X₁ X₂ X₃ : C}

#check ShortComplex
#check ShortComplex.Hom
#synth Category (ShortComplex C)

example (X : C) : ShortComplex C where
  f := (0 : X ⟶ X)
  g := (0 : X ⟶ X)

example {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₃) :
    (φ ≫ ψ).τ₂ ≫ S₃.g = S₁.g ≫ (φ ≫ ψ).τ₃ := (φ ≫ ψ).comm₂₃

variable (S : ShortComplex C)

/-!
左同调数据表示：取 `g` 的核，
然后取诱导映射到该核的余核。
右同调数据表示对偶的概念。同调数据同时包含两者，
外加两个结果之间的相容同构。
-/

#check ShortComplex.LeftHomologyData
#check ShortComplex.RightHomologyData
#check ShortComplex.HomologyData
#check ShortComplex.HasHomology
#check ShortComplex.homology
#check ShortComplex.Exact
#check ShortComplex.Exact.op
#check ShortComplex.HomologyData.ofAbelian
#check Abelian.freyd_mitchell

section HasHomology

variable [S.HasHomology]

#check (S.homology : C)
#check (S.cycles : C)
#check (S.opcycles : C)
#check (S.homologyπ : S.cycles ⟶ S.homology)
#check (S.homologyι : S.homology ⟶ S.opcycles)
#check S.homologyIsCokernel
#check S.homologyIsKernel

end HasHomology

end ShortComplexes

/-!
## 复形形状

我们没有将后继函数内嵌到微分的类型中。
相反，形状是一个关系，规定了微分允许在何处非零。
-/

section ComplexShapes

variable {ι : Type*}

#check ComplexShape
#check ComplexShape.up
#check ComplexShape.down
#check ComplexShape.symm
#check ComplexShape.up'

example (c : ComplexShape ι) {i j j' : ι} (hij : c.Rel i j) (hij' : c.Rel i j') :
    j = j' :=
  c.next_eq hij hij'

example (c : ComplexShape ι) {i i' j : ι} (hij : c.Rel i j) (hi'j : c.Rel i' j) :
    i = i' :=
  c.prev_eq hij hi'j

end ComplexShapes

/-!
## 同调复形
-/

section HomologicalComplexes

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable (c : ComplexShape ι)

#check HomologicalComplex
#check HomologicalComplex.X
#check HomologicalComplex.d
#check HomologicalComplex.shape
#check HomologicalComplex.d_comp_d

example (X : ι → V) : HomologicalComplex V c where
  X := X
  d := fun _ _ => 0

variable (K : HomologicalComplex V c) (i j k : ι)

example (hij : ¬ c.Rel i j) : K.d i j = 0 :=
  K.shape i j hij

example : K.d i j ≫ K.d j k = 0 :=
  K.d_comp_d i j k

/-!
短复形 API 在每个指标处被复用。`sc' i j k` 是
短复形 `X i ⟶ X j ⟶ X k`；`sc j` 是使用 `c.prev j` 和 `c.next j` 的那个。
-/

#check HomologicalComplex.shortComplexFunctor'
#check HomologicalComplex.shortComplexFunctor
#check HomologicalComplex.sc'
#check HomologicalComplex.sc

#check (K.sc' i j k : ShortComplex V)
#check (K.sc j : ShortComplex V)

example : (K.sc' i j k).f = K.d i j := rfl
example : (K.sc' i j k).g = K.d j k := rfl

/-!
当指标在命题上相等时，mathlib 将传递包装为同构。
-/

#check HomologicalComplex.XIsoOfEq

example : K.XIsoOfEq (rfl : i = i) = Iso.refl _ := by
  simp

section HasHomology

#check K.HasHomology

example [K.HasHomology j] : K.iCycles j ≫ K.d j k = 0 :=
  K.iCycles_d j k

end HasHomology

section homology

variable (hi : c.prev j = i) (hk : c.next j = k)
variable [K.HasHomology j] [(K.sc' i j k).HasHomology]

#check HomologicalComplex.homologyIsoSc'

end homology

end HomologicalComplexes

/-!
## 谱序列

有了这些准备，谱序列有一个简洁的接口：
每一页都是一个同调复形，其中一页的同调
与下一页等同。
-/

section SpectralSequences

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

#check SpectralSequence

variable (E : SpectralSequence C c r₀)
variable (pq : κ) (r r' : ℤ) (hr : r₀ ≤ r) (hrr' : r + 1 = r')

#check SpectralSequence.pageXIsoOfEq

/-- 从第 `r₀` 页开始的上同调谱序列。
其页面是双分级复形 `E_r^{p,q}`，第 `r` 页上的微分
`E_r^{p,q} ⟶ E_r^{p+r,q-r+1}` 具有次数 `(r, 1 - r)`。-/
def CohomologicalSpectralSequence' (r₀ : ℤ) : Type _ :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀

end SpectralSequences
