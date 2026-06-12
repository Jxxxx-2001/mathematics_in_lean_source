module

public import Mathlib

section DerivedFunctor

-- 导出函子的经典构造

#check CategoryTheory.injectiveResolutions

#check CategoryTheory.Functor.rightDerivedToHomotopyCategory

#check CategoryTheory.Functor.rightDerived

-- 相关问题

#check CategoryTheory.Tor
#check CategoryTheory.Tor'

-- 目前我们无法统一这两者

#check Rep.Tor

-- 定义为左导出（失去了典范性）

end DerivedFunctor

section Ext

-- 同调复形的一般拟同构
#check HomologicalComplexUpToQuasiIso

-- 具体化为 `ℤ` 上链复形
#check DerivedCategory

#check CategoryTheory.ShiftedHom

#check CategoryTheory.Localization.SmallShiftedHom

#check CategoryTheory.Abelian.Ext

-- （非常典范的）杯积，同时也是长正合列的组成部分

#check CategoryTheory.ShiftedHom.comp
#check CategoryTheory.Abelian.Ext.comp

-- 对于 `Ext X Y 0`

#check CategoryTheory.ShiftedHom.mk₀
#check CategoryTheory.Abelian.Ext.mk₀

-- 对于连接同态

#check CategoryTheory.ShortComplex.ShortExact.singleδ
#check CategoryTheory.ShortComplex.ShortExact.extClass

-- 正合函子下的映射

#check CategoryTheory.Abelian.Ext.mapExactFunctor

#check CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀

#check CategoryTheory.Abelian.Ext.mapExactFunctor_comp

#check CategoryTheory.Abelian.Ext.mapExactFunctor_extClass

section Applications

-- 层上同调实现为 `Ext`
#check CategoryTheory.Sheaf.H

-- 同调维数
#check CategoryTheory.projectiveDimension
#check CategoryTheory.injectiveDimension

end Applications

end Ext

section ModuleCat

-- 投射
#check Module.Projective
#check CategoryTheory.Projective
#check IsProjective.iff_projective

-- 内射
#check Module.Injective
#check CategoryTheory.Injective
#check Module.injective_iff_injective_object

#check Module.Baer
#check Module.Baer.extension_property
#check Module.Baer.iff_injective

end ModuleCat

section IsomorphismTheorems

-- 基本构造
#check Ideal.map
#check Ideal.comap
#check Submodule.map
#check Submodule.comap

-- 基本构造
#check Submodule.Quotient.mk
#check Submodule.mkQ
#check Ideal.Quotient.mk
#check Ideal.Quotient.mkₐ

#check Submodule.liftQ
#check Ideal.Quotient.lift
#check Ideal.Quotient.liftₐ

#check Submodule.mapQ
#check Ideal.quotientMap
#check Ideal.quotientMapₐ

-- 第一同构定理及其变体
#check RingHom.quotientKerEquivOfSurjective
#check RingHom.quotientKerEquivRange
#check LinearMap.quotKerEquivOfSurjective
#check LinearMap.quotKerEquivRange

-- 中国剩余定理
#check Ideal.quotientInfRingEquivPiQuotient

-- 第二同构定理
#check LinearMap.quotientInfEquivSupQuotient

-- 第三同构定理及其变体
#check Submodule.quotientQuotientEquivQuotient
#check Submodule.quotientQuotientEquivQuotientSup

end IsomorphismTheorems

section Nakayama

#check Submodule.eq_smul_of_le_smul_of_le_jacobson

end Nakayama

section MorphismHierarchy

-- 不要创建任何接受态射类项作为参数的新定义！
--https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Mathlib.27s.20morphism.20hierarchy/near/554383157

-- 已经存在一些不好的东西
#check IsLocalHom
#check RingHom.ker

-- 我们已经通过层级有了下降系统

end MorphismHierarchy

section Localization

-- 局部化的实现

#check IsLocalization
#check Localization
#check Localization.AtPrime

#check IsLocalizedModule
#check LocalizedModule
#check LocalizedModule.AtPrime

-- 泛性质通过 "is" 版本陈述

#check IsLocalization.lift

#check IsLocalizedModule.lift

end Localization

section TensorProduct

-- 按照我们通常的做法实现
#check TensorProduct

-- 泛性质
#check TensorProduct.lift
#check TensorProduct.lift.unique

-- 关于同构：使用 loogle 和 leansearch

-- 重要的同构
#check TensorProduct.lid
#check Algebra.TensorProduct.lid
#check TensorProduct.comm
#check Algebra.TensorProduct.comm
#check TensorProduct.assoc
#check Algebra.TensorProduct.assoc

-- "is" 版本
#check IsTensorProduct
#check IsBaseChange

end TensorProduct

section DimensionTheory

-- 对环而言
#check ringKrullDim
#check Ideal.height

-- Krull 高度定理
#check Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
#check Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes

-- 其他有用的结果
#check Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes
#check Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown

-- 多项式
#check Polynomial.ringKrullDim_le
#check Polynomial.ringKrullDim_of_isNoetherianRing

-- 对模而言
#check Module.supportDim

-- 关键引理
#check PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last

#check Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
#check Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
#check Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson

end DimensionTheory

section Completion

#check Ideal.Filtration

#check reesAlgebra

#check Ideal.Filtration.submodule

-- Artin-Rees
#check Ideal.exists_pow_inf_eq_pow_smul
-- 局部环的 Krull 交
#check Ideal.iInf_pow_eq_bot_of_isLocalRing
-- 整环的 Krull 交
#check Ideal.iInf_pow_eq_bot_of_isDomain

variable (R :Type*) [CommRing R] (I : Ideal R)
-- 关联分级环
#check (reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))

end Completion

section Flat

#check Module.Flat

-- 通过有限生成理想
#check Module.Flat.iff_rTensor_injective
#check Module.Flat.iff_lTensor_injective

-- 等式判则
#check Module.Flat.exists_factorization_of_apply_eq_zero_of_free

-- 从平坦推出自由
#check Module.free_of_flat_of_isLocalRing

end Flat

section Integral

#check Algebra.IsIntegral

-- 整闭，但针对分式环而非整环
#check IsIntegrallyClosedIn
#check IsIntegrallyClosed

-- GU（Going Up）
#check Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime

-- GD（Going Down）
#check instHasGoingDownOfIsDomainOfFaithfulSMulOfIsIntegralOfIsIntegrallyClosed

end Integral
