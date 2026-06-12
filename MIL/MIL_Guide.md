# Mathematics in Lean (MIL) 学习指南

本指南按章节逐一说明 MIL 目录下每个 Chapter 和 Section 的核心内容、重要结论以及需要注意的知识点。

---

# 第1章：引言（C01_Introduction）

## 章节概述

本章是最简短的入门，介绍 Lean 环境的基本使用方式，以及类型（Type）、项（Term）、值（Value）、证明（Proof）之间的关系（Curry-Howard 对应）。

---

### S01: Getting Started

**讲授内容：**
- 如何使用 `#eval` 在 Lean 中求值表达式。
- 运行一个 "Hello, World!" 来验证环境正常。

**重要结论：** 无（纯环境搭建）。

**注意要点：**
- `#eval "Hello, World!"` 是 Lean 中的 "Hello World"。

---

### S02: Overview

**讲授内容：**
- 类型、项、值和证明之间的关系（Curry-Howard 同构）。
- 三种声明：`def`（数据）、`theorem`（命题）、`lemma`（命题）。
- `#check` 检查表达式类型；`#eval` 求值；`#print` 查看定义。
- 命题的类型是 `Prop`。
- `example`、`theorem`、`lemma`、`def` 的区别。
- `rfl` 作为自反性证明（`a = a`）。
- `sorry` 作为未完成证明的占位符。
- `Even` 的定义（存在 `k` 使得 `n = k + k`）。
- 多种证明风格：项风格、`by ...` 策略块风格、`rintro`/`use`/`rw`/`ring` 组合、`parity_simps` 简化。

**重要结论：**
- `theorem easy : 2 + 2 = 4 := rfl` —— 最简单的等式证明。
- `∀ m n : Nat, Even n → Even (m * n)` —— 用五种不同风格证明。

**注意要点：**
- `rfl` 只能证明 `a = a`（定义相等）。
- `⟨k, hk⟩` 是结构/对偶构造器（存在性见证+证明）。
- `rw [hk, mul_add]` 使用假设 `hk` 和引理 `mul_add` 进行重写。
- `ring` 是处理环表达式的策略。
- `rintro m n ⟨k, hk⟩` 同时引入变量并解构存在量词。
- `use m * k` 提供存在性见证。

---

# 第2章：基础（C02_Basics）

## 章节概述

本章教授 Lean 中代数操作的基本证明技术。涵盖 `rw` 重写、`calc` 计算块、`ring` 自动化策略、环/群公理、库引理的使用、不等式推理、代数结构以及 `Nat` 上的整除性。

---

### S01: Calculating

**讲授内容：**
- `rw` 策略进行等式重写。
- `▸`（`Eq.subst`）进行项级别替换。
- `mul_comm`、`mul_assoc`、`mul_add`、`add_mul` 等代数重写引理。
- `calc` 块：链式等式的可读写法。
- `rw [h] at hyp`：在假设中重写。
- `ring` 策略：自动处理交换环上的多项式恒等式。
- `nth_rw`：重写特定位置的项。
- `←`：从右向左重写。
- `section` 和 `variable` 机制。

**重要结论：**
- `(a + b) * (a + b) = a * a + 2 * (a * b) + b * b`（用 `ring`）。
- `(a + b) * (a - b) = a ^ 2 - b ^ 2`（用 `ring`）。

**注意要点：**
- `rw` 可以接受引理列表：`rw [h', ← mul_assoc, h, mul_assoc]`。
- `calc` 中使用 `_ = ... := by ...` 链式证明。
- `ring` 仅在 `CommRing` 中完全自动化。
- `nth_rw 2 [h]` 只重写第二个匹配项。
- `exact hyp` 直接用假设关闭目标。

---

### S02: Proving Identities in Algebraic Structures

**讲授内容：**
- 使用 `#check` 查看环公理：`add_assoc`、`add_comm`、`zero_add`、`neg_add_cancel`、`mul_assoc`、`mul_one`、`one_mul`、`mul_add`、`add_mul`。
- `CommRing` vs `Ring`。
- 创建命名空间 `MyRing` 从公理证明环恒等式。
- 推导环公理的推论：`add_zero`、`add_neg_cancel`、`mul_zero`、`zero_mul`、`neg_neg` 等。
- `have` 在证明中创建辅助引理。
- `AddGroup` vs `Ring` vs `Group`。
- 群公理推导：`mul_inv_cancel`、`mul_one`、`mul_inv_rev`。

**重要结论：**
- `mul_zero (a : R) : a * 0 = 0`（使用 `add_left_cancel`）。
- `neg_neg (a : R) : - -a = a`。
- `mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹`。

**注意要点：**
- 命名空间隔离（`MyRing` vs `MyGroup`）防止与 Mathlib 名称冲突。
- 许多环恒等式从公理 + `add_left_cancel`/`add_right_cancel` 推导。
- `norm_num` 处理数值算术。
- `apply` 使用引理的结论匹配目标。
- `ring` 只在 `CommRing` 中工作，不在普通 `Ring` 中。

---

### S03: Using Theorems and Lemmas

**讲授内容：**
- 基本不等式定理：`le_refl`、`le_trans`、`lt_of_le_of_lt`、`lt_of_lt_of_le`、`lt_trans`。
- 定理作为函数：`le_trans h₀ h₁`。
- 命名参数：`(b := y)`。
- `apply` vs `exact` vs `refine`。
- `linarith`：线性（不）等式的全自动策略。
- `exp_le_exp.mpr`：使用 `↔` 的 `.mpr` 方向。
- 单调性引理：`add_le_add`、`add_le_add_right`、`add_lt_add_of_le_of_lt`、`add_nonneg`、`add_pos`。
- `sq_nonneg a : 0 ≤ a^2`。
- `log_le_log` 要求参数为正。

**重要结论：**
- `2*a*b ≤ a^2 + b^2`（通过 `(a-b)^2 ≥ 0` 和 `linarith`）。
- `log (1 + exp a) ≤ log (1 + exp b)` 若 `a ≤ b`。

**注意要点：**
- `linarith` 消化所有可用假设和线性目标。
- `exp_le_exp.mpr` 访问 `↔` 的前向方向。
- `apply` 将目标变为定理的前提。
- `have h : ... := ...` 创建新命名事实。

---

### S04: More on Order and Divisibility

**讲授内容：**
- `min` 和 `max` 函数：`min_le_left`、`le_min`、`le_max_left`、`max_le` 等。
- `le_antisymm` 从两个不等式证明相等。
- `show` 策略：标注子目标。
- `repeat` 策略：重复应用策略块。
- 三角不等式 `abs_add_le`：`|a+b| ≤ |a| + |b|`。
- `Nat` 上的整除性 `x ∣ y`：`dvd_trans`、`dvd_mul_of_dvd_left`、`dvd_mul_left`、`dvd_mul_right`。
- `Nat.gcd` 和 `Nat.lcm` 定理。

**重要结论：**
- `min a b = min b a`（min 的交换性）。
- `|a| - |b| ≤ |a - b|`（反向三角不等式）。

**注意要点：**
- `le_antisymm` 是证明 `≤` 双向相等的标准方法。
- `show` 不改变目标，仅作标注。
- `abs_add_le` 是实数上的三角不等式。
- `Nat` 上的整除性使用 `Nat` 定理，但符号 `∣` 相同。

---

### S05: Proving Facts about Algebraic Structures

**讲授内容：**
- `PartialOrder` 及其公理：`le_refl`、`le_trans`、`le_antisymm`。
- `lt_iff_le_and_ne`：`x < y ↔ x ≤ y ∧ x ≠ y`。
- `Lattice`：`⊓`（交/下确界）和 `⊔`（并/上确界）。
- `DistribLattice`：分配律 `inf_sup_left`、`sup_inf_left` 等。
- `IsStrictOrderedRing`：与乘法兼容的严格序环。
- `MetricSpace`：`dist_self`、`dist_comm`、`dist_triangle`。

**重要结论：**
- `x ⊓ y = y ⊓ x`（交的交换性）。
- `x ⊔ y = y ⊔ x`（并的交换性）。
- 吸收律：`x ⊓ (x ⊔ y) = x`、`x ⊔ (x ⊓ y) = x`。
- `0 ≤ dist x y`（距离的非负性）。

**注意要点：**
- `⊓` 和 `⊔` 是 Unicode 中缀运算符。
- `calc` 也可用于 `≤` 链，不仅是 `=`。
- 类型类组合：`[Ring R] [PartialOrder R] [IsStrictOrderedRing R]`。
- 度量空间用 `dist` 作为距离函数。

---

# 第3章：逻辑（C03_Logic）

## 章节概述

本章系统性地涵盖 Lean 中的核心逻辑连接词和量词，并将它们与依值类型论联系起来。每个 Section 处理一个连接词：如何构造证明（引入规则）和如何使用/消除证明（消除规则）。从 `∀` 和 `→` 开始，经过 `∃`、`¬`、`∧`/`↔`、`∨`，最终将所有逻辑工具应用于证明 `ℝ` 中序列收敛的性质。

---

### S01: Implication and the Universal Quantifier

**讲授内容：**
- Curry-Howard 对应：`∀ x : ℝ, 0 ≤ x → |x| = x` 是一个依值函数类型。
- `→` 是蕴涵，也是函数类型。
- `∀` 是限制在 `Prop` 上的 `Π`（依值积）。
- `intro` 策略：证明 `∀ x, P x` 或 `P → Q`。
- `abs_of_nonneg hx`：从 `0 ≤ x` 得 `|x| = x`。
- 项证明：`fun x => ...` / `fun hx => ...`。
- 柯里化：嵌套 `∀` 的语法糖。
- 隐式参数 `{x y ε : ℝ}`。
- `FnUb`（函数上界）、`FnLb`（函数下界）。
- `Monotone f`、`FnEven`（偶函数）、`FnOdd`（奇函数）。
- `Set α` 同构于 `α → Prop`；子集 `s ⊆ t` 是 `∀ x, x ∈ s → x ∈ t`。
- `Injective` 单射性。

**重要结论：**
- 单调函数的和、数乘、复合仍是单调的。
- 偶函数之和为偶、奇函数之积为偶、偶奇复合为偶。
- `x + c` 是单射、`c * x`（`c ≠ 0`）是单射、单射的复合是单射。

**注意要点：**
- `∀` 和 `→` 在 `Prop` 层面都是函数类型。
- `intro` 是 `∀` 和 `→` 的唯一引入规则。
- `Set α = α → Prop`，因此 `x ∈ s` 就是 `s x`。
- `Injective f` 即 `∀ {a b}, f a = f b → a = b`。

---

### S02: The Existential Quantifier

**讲授内容：**
- `∃ x : ℝ, P x` 是存在量词。
- `Exists`（`Prop` 版）vs `Sigma`（数据版）。
- `Exists.intro` 和 `Exists.elim`。
- `use` 策略：提供见证并拆分证明。
- `⟨witness, proof⟩` 语法。
- `rcases h with ⟨w, p⟩`、`rintro`、`obtain`、`cases`、`match`。
- `Brahmagupta-Fibonacci` 恒等式：两平方和的乘积是平方和。
- `a ∣ b` 即 `∃ d, b = a * d`。
- `Surjective f`：`∀ y, ∃ x, f x = y`。

**重要结论：**
- 两平方和的乘积是平方和。
- 整除的传递性：`a∣b` 且 `b∣c` 蕴涵 `a∣c`。
- 满射的复合是满射。

**注意要点：**
- `∃` 引入：提供见证+性质证明。
- `∃` 消除：`rcases`、`cases`、`match` 提取见证和证明。
- `use` 是方便的提供见证策略。
- `field_simp [h]` 在分母非零假设下简化有理表达式。

---

### S03: Negation

**讲授内容：**
- `¬ P` 定义为 `P → False`。
- 证明 `¬P`：`intro h` 假设 `P`，推导 `False`。
- `lt_irrefl` 导出 `a < a` 的矛盾。
- `linarith` 可检测矛盾。
- `by_contra h`：反证法。
- `push_neg`：将 `¬` 推过 `∀` 和 `∃`。
- `contrapose!`：转换为逆否命题并推入否定。
- `exfalso`：将目标变为 `False`。
- `absurd h h'`、`contradiction`。

**重要结论：**
- 经典原理：`¬∀ x, P x → ∃ x, ¬P x`（需经典逻辑）。
- 双重否定消除 `¬¬Q → Q` 是经典的。
- Epsilon 原理：若对所有 `ε > 0` 有 `x < ε`，则 `x ≤ 0`。

**注意要点：**
- `¬P` 就是函数 `P → False`。
- `by_contra h` 对当前目标使用反证法。
- `push_neg` 和 `contrapose!` 自动化否定推入。
- 经典原理在构造性逻辑中不可证，需要 `by_contra` 或 `by_cases`。

---

### S04: Conjunction and Iff

**讲授内容：**
- `P ∧ Q`（合取）：打包两个证明。
- 引入：`constructor` 或 `⟨h₁, h₂⟩`。
- 消除：`rcases h with ⟨h₁, h₂⟩`、`h.left`/`h.right`。
- `P ↔ Q` 即 `(P → Q) ∧ (Q → P)`。
- 证明 `↔`：`constructor` 创建两个方向。
- `.mpr`/`.mp` 访问 `↔` 的正向/反向。
- `abs_lt`：`|x| < y ↔ -y < x ∧ x < y`。
- `Nat.dvd_gcd_iff`：`d ∣ Nat.gcd m n ↔ d ∣ m ∧ d ∣ n`。
- `lt_iff_le_not_ge`。

**重要结论：**
- `x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0`。
- `¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y`。

**注意要点：**
- `∧` 类比于 `Prop` 中的积/对偶类型。
- `↔` 类比于一对函数（正向和反向）。
- `abs_lt` 将单个绝对值不等式转换为合取。
- `constructor <;> tactic` 将策略应用于两个子目标。

---

### S05: Disjunction

**讲授内容：**
- `P ∨ Q`（析取）：两个构造器 `Or.inl`（左）和 `Or.inr`（右）。
- 引入：`left`/`right` 策略。
- 消除：`rcases h with h | h` 分成两种情况。
- `le_or_gt`（三分律引理：`a ≤ b` 或 `a > b`）。
- `lt_trichotomy`（三向分类：`a < b`、`a = b`、`a > b`）。
- `by_cases h : P`：对任意命题进行经典情况分析。
- `em P`（排中律：`P ∨ ¬P`）。

**重要结论：**
- `x^2 = 1 → x = 1 ∨ x = -1`（在整环中）。
- `(P → Q) ↔ (¬P ∨ Q)`（经典逻辑中等价）。

**注意要点：**
- `left`/`right` 选择证明析取的哪一侧。
- `le_or_gt` 是对实数不等式进行分类讨论的关键引理。
- `by_cases h : P` 是策略级别的排中律。
- `Or` 消除需要在两种可能情况下证明同一目标。

---

### S06: Sequences and Convergence

**讲授内容：**
- 序列收敛的 ε-N 定义：`ConvergesTo s a := ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε`。
- `ext`、`congr`、`convert` 策略。
- 常数列收敛、和的极限、常数倍的极限。
- 收敛序列最终有界（用 `ε = 1`）。
- 乘积的极限（利用有界性）。
- 极限的唯一性。
- 将 `ConvergesTo` 推广到任意 `LinearOrder α` 作为索引集。

**重要结论：**
- `convergesTo_add`：和的极限等于极限之和（使用 `ε/2` 技巧）。
- `convergesTo_mul`：乘积的极限等于极限之积。
- `convergesTo_unique`：极限是唯一的（通过 `|a-b|/2` 和三角不等式导出矛盾）。

**注意要点：**
- ε-N 定义直接表示为嵌套的 `∀ ε, ∃ N, ∀ n` 公式。
- `linarith` 对 ε 操作（如 `0 < ε/2`）很有用。
- `max Ns Nt` 用于同步两个收敛阈值。
- `by_cases h : c = 0` 处理退化情况。
- `ext` 将函数相等展开为 `∀ x, f x = g x`。

---

# 第4章：集合与函数（C04_Sets_and_Functions）

## 章节概述

本章介绍集合和函数在 Lean 中的数学形式化，从基本集合运算到函数的像/原像，最终完成 Schröder-Bernstein 定理的完整证明。

---

### S01: Sets

**讲授内容：**
- `Set α` 类型（本质是 `α → Prop`）。
- 基本集合运算：交集 `∩`、并集 `∪`、差集 `\`、集合构造式。
- 索引并集 `⋃ i, A i` 和索引交集 `⋂ i, A i`。
- 集族 `⋃₀ s`（sUnion）和 `⋂₀ s`（sInter）。

**重要结论：**
- `s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`（分配律）。
- `s ∩ t = t ∩ s`（交的交换性）。
- `evens ∪ odds = univ`（需要经典排中律）。
- `(⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 }`。

**注意要点：**
- `ext x` 将集合相等归约为成员等价。
- `simp [mem_inter_iff, mem_iUnion]` 展开集合成员定义。
- 索引并集/交集的 `mem_iUnion` 和 `mem_iInter` 引理。
- 集合论语句可归约为命题逻辑。

---

### S02: Functions

**讲授内容：**
- 函数的像 `f '' s` 和原像 `f ⁻¹' u`。
- 像与原像之间的 Galois 连接：`f '' s ⊆ v ↔ s ⊆ f ⁻¹' v`。
- `InjOn f s`：在集合 `s` 上单射。
- `Classical.choose` 和 `Classical.choose_spec` 构造伪逆。
- Cantor 定理：`∀ f : α → Set α, ¬Surjective f`。

**重要结论：**
- `f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v`（原像保持交，由 `rfl` 直接可得）。
- `f '' (s ∪ t) = f '' s ∪ f '' t`（像保持并）。
- 单射 `f` 下：`f ⁻¹' (f '' s) ⊆ s`。
- 满射 `f` 下：`u ⊆ f '' (f ⁻¹' u)`。
- `Injective f ↔ LeftInverse (inverse f) f`。
- `Surjective f ↔ RightInverse (inverse f) f`。
- Cantor 定理：不存在到其幂集的满射。

**注意要点：**
- 像的成员是 `∃ x ∈ s, f x = y`。
- Galois 连接是像/原像理论的核心。
- 对角集 `{ i | i ∉ f i }` 是 Cantor 定理证明的关键构造。
- `noncomputable` 标记使用经典选择的定义。

---

### S03: The Schroeder-Bernstein Theorem

**讲授内容：**
- 完整的 Schröder-Bernstein 定理证明。
- 分层构造（stratification）：递归定义 `sbAux : ℕ → Set α`。
- 混合函数 `sbFun`：在分层集上用 `f`，在补集上用 `invFun g`。
- 单射性和满射性的分别证明。

**重要结论：**
- **Schröder-Bernstein 定理**：若存在单射 `f : α → β` 和 `g : β → α`，则存在双射 `h : α → β`。

**注意要点：**
- `wlog` 用于对称情况处理。
- `set A := sbSet f g with A_def` 用于命名集合。
- `invFun g` 尝试选取原像；`leftInverse_invFun hg` 给出左逆。
- 这是全书最复杂的证明之一，展示了 Lean 中构造性集合论证明的完整流程。

---

# 第5章：初等数论（C05_Elementary_Number_Theory）

## 章节概述

将 Lean 应用于初等数论：通过奇偶性和素因子分解证明无理数、自然数上的归纳与递归、Euclid 素数无穷证明以及更高级的归纳模式。

---

### S01: Irrational Roots

**讲授内容：**
- 证明 `√2` 是无理数（`m^2 ≠ 2*n^2` 当 `m, n` 互素）。
- 推广到任意素数 `p`。
- 使用因子分解指数（`factorization`）的更一般陈述。
- `Nat.Coprime`、`Nat.Prime` 基础。

**重要结论：**
- `2 ∣ m^2 → 2 ∣ m`（核心引理）。
- 互素的 `m, n` 满足 `m^2 ≠ 2 * n^2`。
- 推广：互素的 `m, n` 对任何素数 `p` 满足 `m^2 ≠ p * n^2`。
- 用因子分解指数的奇偶性给出更一般的不可解条件。

**注意要点：**
- `Nat.Prime.dvd_of_dvd_pow` 简化了 `2 ∣ m^2 → 2 ∣ m` 的证明。
- `Nat.factorization` 是素指数映射；`factorization_mul'`、`factorization_pow'` 是关键引理。
- `multiplicity` 提供了另一种描述因子出现次数的方法。

---

### S02: Induction and Recursion

**讲授内容：**
- 自然数的归纳和递归。
- 阶乘的归纳证明：`fac_pos n`、`dvd_fac`。
- `Finset.sum` 和 `Finset.prod`：`∑` 和 `∏` 记号。
- `range n` 上的和与积。
- 自定义归纳类型 `MyNat` 及其算术运算。

**重要结论：**
- `fac n = ∏ i ∈ range n, (i+1)`（阶乘作为乘积）。
- `∑ i ∈ range (n+1), i = n*(n+1)/2`（三角形数公式）。
- `∑ i ∈ range (n+1), i^2 = n*(n+1)*(2*n+1)/6`。

**注意要点：**
- `Finset.sum_range_succ` 和 `Finset.prod_range_succ` 是处理范围和/积的关键。
- `MyNat` 练习通过显式递归定义加法/乘法，教授递归结构与归纳证明之间的关系。
- `noConfusion` 编码构造器互斥和单射性。

---

### S03: Infinitely Many Primes

**讲授内容：**
- `two_le`：多种证明风格展示（`cases`、`induction`、`by_contra`、`interval_cases`、`decide`）。
- 强归纳：`Nat.strong_induction_on`。
- Euclid 素数无穷证明。
- Finset 版本的素数无穷证明。
- 模 4 余 3 的素数无穷多。

**重要结论：**
- `exists_prime_factor`：若 `2 ≤ n`，则存在素因子。
- `primes_infinite`：对任意 `n`，存在 `p > n` 的素数。
- `primes_mod_4_eq_3_infinite`：模 4 余 3 的素数无穷多。

**注意要点：**
- 强归纳 `Nat.strong_induction_on` 允许假设对所有 `m < n` 成立。
- Euclid 证明的关键：`N = n! + 1` 的素因子不在 `≤ n` 范围内。
- `interval_cases` 对有限情况进行穷举。
- 模 4 余 3 的推广证明使用 `Finset` 收集已知素数并构造矛盾。

---

### S04: More Induction

**讲授内容：**
- 阶乘的四种不同归纳风格。
- Fibonacci 数列：`fib` 定义、Binet 公式、尾递归版本、加法公式。
- `generalizing` 泛化归纳假设。
- 每个整数 `≠ 1` 有素因子。

**重要结论：**
- **Binet 公式**：`fib n = (φ^n - φ'^n)/√5`（其中 `φ = (1+√5)/2`）。
- 连续 Fibonacci 数互素。
- 尾递归 `fib'` 等价于 `fib`，且可高效计算 `fib' 10000`。
- **Fibonacci 加法公式**：`fib (m+n+1) = fib m * fib n + fib (m+1) * fib (n+1)`。
- `n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n`。

**注意要点：**
- `induction n generalizing m` 在归纳期间保持参数 `m` 全称量化。
- 尾递归对高效计算至关重要。
- Binet 公式的证明结构镜像 `fib` 的三分叉定义。
- `Nat.not_prime_iff_exists_dvd_lt` 用于非素数的分解。

---

# 第6章：离散数学（C06_Discrete_Mathematics）

## 章节概述

涵盖有限集合（`Finset`）、有限类型（`Fintype`）、基数计数论证、鸽巢原理、双重计数以及归纳数据结构（列表、二叉树、命题公式）。

---

### S01: Finsets and Fintypes

**讲授内容：**
- `Finset α`（有限子集）vs `Fintype α`（类型本身有限）。
- `Finset` 需要 `[DecidableEq α]`。
- 集合字面量 `{0, 2, 5}`、过滤 `s.filter P`、像、积、幂集。
- `Finset` 底层基于 `Multiset`。
- `Finset.induction_on` 归纳。
- `Finset.card` 和 `Fintype.card`。
- `Fintype` 提供 `Finset.univ`。

**重要结论：**
- `Fintype.card (Fin 5) = 5`。
- 积类型基数相乘、和类型基数相加。
- 将 Finset 强制转换为类型（子类型），基数保持一致。

**注意要点：**
- `Finset` 需要可判定相等性以保证元素唯一性。
- `Finset.induction_on` 用于关于有限集的证明。
- `#s` 是 `s.card` 的记号。
- `Finset` 操作函数（不像 `Set` 那样是命题），因此本质上是可计算的。

---

### S02: Counting Arguments

**讲授内容：**
- 基数公式：`#(s ×ˢ t) = #s * #t`、`#(s ∪ t) = #s + #t - #(s ∩ t)`。
- `card_image_of_injective`：单射下像的基数不变。
- `Fintype` 基数：积、和、函数空间。
- 三角形数 `triangle n` 的三种证明。
- 双重计数模板。
- 鸽巢原理应用。

**重要结论：**
- 三角形数三种证法：按第二坐标分区、与 `Σ` 类型的双射、旋转映射。
- 双重计数：`∑ a ∑ b indicator = ∑ b ∑ a indicator`（求和交换 `sum_comm`）。
- 鸽巢原理：从 `2n` 个数中取 `n+1` 个，必有两个互素。

**注意要点：**
- `Fintype.card_congr` 通过双射证明基数相等。
- `card_biUnion` 用于不交并的基数。
- `sum_comm` 是双重计数的核心。
- `exists_lt_card_fiber_of_mul_lt_card_of_maps_to` 是鸽巢原理的通用形式。

---

### S03: Inductive Structures

**讲授内容：**
- 自定义列表类型及 `append`、`map`、`reverse`。
- 列表定理：`append_nil`、`map_map`。
- 二叉树：`BinTree`、`size`、`depth`。
- 命题公式：`PropForm`、`eval`（求值）、`vars`（变量）、`subst`（替换）。

**重要结论：**
- `map (g ∘ f) as = map g (map f as)`。
- `size t ≤ 2^depth t - 1`（二叉树大小上界）。
- 若两个赋值在公式的变量上一致，则求值相同。
- 替换不在公式变量中的变量不改变公式。

**注意要点：**
- 结构归纳法：对每个构造器逐一处理。
- `cases A` 对归纳类型进行情况分析。
- `simp_all` 结合递归调用处理结构归纳。
- 归纳结构是函数式编程和定理证明的基础。

---

# 第7章：结构体（C07_Structures）

## 章节概述

本章介绍 Lean 的 `structure` 命令，用于定义带命名字段的新数据类型，这是 Lean 中编码数学核心概念的方式。然后将代数公理打包为结构体（群、环），展示 `structure` 和 `class` 的区别，最后通过构建高斯整数并证明其构成欧几里得整环作为综合案例。

---

### S01: Structures

**讲授内容：**
- 用 `structure` 定义类型，用 `@[ext]` 自动派生外延性引理。
- 多种构造方式：命名域语法 `where`、花括号、`⟨...⟩`、`StructureName.mk`。
- 自定义构造器名（`build` 关键字）。
- 子类型 `{ y : ℝ // 0 < y }`（带属性的 Σ 类型）。
- 依值积 `Σ n : ℕ, StandardSimplex n`。
- 带证明域的结构体。

**重要结论：**
- `Point.add_comm`：使用 `ext`、`dsimp`、`add_comm`。
- `StandardTwoSimplex.midpoint`：保持非负性和和为 1 的中点构造。

**注意要点：**
- `@[ext]` 自动生成 `.ext` 引理。
- `⟨⟩` 匿名构造器 vs 命名 `where` 语法。
- 结构体的模式匹配。
- `ext <;> repeat' tactic` 模式。

---

### S02: Algebraic Structures

**讲授内容：**
- 定义群结构 `Group₁ α`（纯 `structure`，打包运算和公理）。
- `Grp₁`：将类型与群结构打包在一起。
- `Equiv` 类型（`α ≃ β`）及其性质。
- `permGroup`：置换群的群结构。
- `class` vs `structure`：`class` 启用实例合成。
- `Inhabited` 类型类和 `default` 值。
- 定义 `instance` 提供 `+`、`*` 等记号。

**重要结论：**
- `permGroup`：置换群满足所有群公理。
- `f * g * g⁻¹ = f`。

**注意要点：**
- `structure`（新类型，载体风格）vs `class`（类型类，用于实例合成）。
- `Equiv` 是双射的标准类型。
- 记号 `f.trans g`、`f.symm`。

---

### S03: Building the Gaussian Integers

**讲授内容：**
- 将 `GaussInt` 定义为 `re : ℤ` 和 `im : ℤ` 的结构体。
- 提供 `Zero`、`One`、`Add`、`Neg`、`Mul` 实例。
- 定义各域的 `simp` 引理。
- 证明 `GaussInt` 是 `CommRing`。
- 范数 `norm` 和共轭 `conj` 及其性质。
- 实现 `ℤ` 上的欧几里得除法（余数 `≤ b/2`）。
- 证明 `GaussInt` 是 `EuclideanDomain`。

**重要结论：**
- `norm_nonneg`、`norm_eq_zero`、`norm_mul`、`norm_conj`。
- `Int.abs_mod'_le`：`|mod' a b| ≤ b/2`。
- `norm_mod_lt`：`(x % y).norm < y.norm`（当 `y ≠ 0`）。
- `GaussInt` 是 `EuclideanDomain`。
- 在欧几里得整环中，不可约元 ⇔ 素元。

**注意要点：**
- `ext <;> simp <;> ring` —— 证明积类型环等式规律的标准模式。
- `gcongr` 用于单调性不等式链。
- `Int.mul_ediv_add_emod` 是核心整数除法性质。
- `measure` 函数用于欧几里得整环的良基终止条件。

---

# 第8章：层级体系（C08_Hierarchies）

## 章节概述

本章教授如何在 Lean 中构建和使用类型类层级体系。从使用 `extends` 创建从半群到幺半群到群的链条开始，然后到态射（同态结构和 `MonoidHomClass` 类型类），最后到子对象（子幺半群、子群、子环）。

---

### S01: Basics

**讲授内容：**
- `class` vs `@[class] structure`。
- 自定义记号（`notation`、`infixl`、`postfix`）。
- `extends` 关键字构建类层级。
- 菱形继承。
- `@[to_additive]`：自动生成加法版本。
- 完整代数层级：`Semigroup` → `Monoid` → `Group` → `CommGroup`。
- `Ring` 扩展 `AddGroup`、`Monoid` 和分配律。
- `SMul` 和 `Module` 作为双参数类型类。

**重要结论：**
- `to_additive` 从乘法定义自动生成加法对应。
- `Ring₃ ℤ` 的完整实例。
- `Module₁ R R`（自模）和 `Module₁ ℤ A`（交换群模）。

**注意要点：**
- `extends` 用于构建类型类层级。
- `@[to_additive]` 复制定义到加法设定。
- `export` 导出域名为顶层名称。
- 双参数类型类（`SMul₃`、`Module₁`）。

---

### S02: Morphisms

**讲授内容：**
- `isMonoidHom₁` 作为 `Prop` vs `isMonoidHom₂` 作为结构体。
- `MonoidHom₁`：打包函数 `toFun` 和 `map_one`/`map_mul`。
- `CoeFun` 使同态自动可用作函数。
- `AddMonoidHom₁`、`RingHom₁`（多重继承）。
- `MonoidHomClass` 模式：参数化于 `F`、`M`、`N` 的类型类。
- `outParam` 避免未解的类型类目标。
- `DFunLike`：现代 Mathlib 方法。

**重要结论：**
- `map_inv_of_inv`：对任何 `MonoidHomClass₂` 同态，若 `m*m'=1` 则 `f m*f m'=1`。

**注意要点：**
- `ext` 结构体用于同态。
- `CoeFun` 配合 lambda 指定共域类型。
- `outParam` 对源/目标类型避免 `unsolved` 类型类目标。
- `extends DFunLike` 是标准 Mathlib 方法。

---

### S03: Subobjects

**讲授内容：**
- 定义 `Submonoid₁`：`carrier : Set M`、`mul_mem`、`one_mem`。
- `SetLike`：使子幺半群可用作集合。
- 子类型的 `Monoid` 实例。
- `SubmonoidClass₁` 混合属性。
- 子幺半群的交。
- 从子幺半群构造 `Setoid`（同余关系）。
- `HasQuotient` 和商幺半群。

**重要结论：**
- 子幺半群继承幺半群结构。
- 子幺半群作为同余关系构造商。

**注意要点：**
- `SetLike` 配合 `coe_injective'`。
- 子类型作为 `Subtype`。
- 商构造通过 `Quotient` 和 `Setoid`。

---

# 第9章：群与环（C09_Groups_and_Rings）

## 章节概述

本章将第7章和第8章的机制应用于群论和环论的实际理论。展示了 Mathlib 中可用的广泛定理库。这是一个概览/演示性质的章节，展示许多使用已有 Mathlib 定理的 `example` 块和一些结构化练习。

---

### S01: Groups

**讲授内容：**
- 基本群记号和定理。
- `MonoidHom`：`f.map_mul`、`f.map_inv`。
- `MulEquiv`：群同构。
- `Subgroup`：`H.mul_mem`、`H.inv_mem`。
- 子群运算：`H ⊓ H'`、`H ⊔ H'`、`⊤`、`⊥`。
- `Subgroup.map` 和 `Subgroup.comap`。
- Lagrange 型定理。
- Sylow 定理。
- 置换群、自由群、群作用。
- Cayley 定理。
- 轨道-稳定子定理。
- 商群和同构定理。

**重要结论：**
- `Nat.card G' ∣ Nat.card G`。
- Sylow 定理：`Sylow.exists_subgroup_card_pow_prime`。
- `orbit G x ≃ G ⧸ stabilizer G x`。
- `G ≃ (G ⧸ H) × H`。
- 同构定理。

**注意要点：**
- `group` 策略处理群论恒等式。
- `abel` 策略处理交换群恒等式。
- `MonoidHom.ker`、`MonoidHom.range`。
- `QuotientGroup` 命名空间：`mk'`、`lift`、`quotientKerEquivRange`、`map`。

---

### S02: Rings

**讲授内容：**
- `ring` 策略。
- 单位群 `Rˣ`。
- `RingHom`、子环。
- 理想 `Ideal R`。
- 商环 `R ⧸ I`。
- 理想运算：`I + J`、`I * J`。
- 中国剩余定理（CRT）。
- `IsCoprime` 理想。
- 代数 `Algebra R A`。
- 多项式 `R[X]`：`X`、`C r`、次数、求值、根。
- D'Alembert-Gauss 定理（代数基本定理）。
- 多元多项式 `MvPolynomial`。

**重要结论：**
- 中国剩余定理：`Ideal.quotientInfRingEquivPiQuotient`。
- `ZMod.prodEquivPi`（整数 CRT）。
- `chineseIso`：完整构造。
- `IsAlgClosed ℂ`（复数代数封闭）。
- `X^2 + 1 = (X - I)(X + I)` 在 `ℂ` 上。

**注意要点：**
- `ring` 策略用于环代数。
- `Ideal.Quotient.mk`、`Ideal.Quotient.lift`。
- `Finset` 归纳用于 `isCoprime_Inf`。
- `Equiv.ofBijective` 将单射+满射变为同构。
- `aeval` 和 `aroots` 用于多项式求值和根。

---

# 第10章：线性代数（C10_Linear_Algebra）

## 章节概述

本章涵盖 Lean 中的基础线性代数，从向量空间公理到基、维度和自同态。强调代数概念（向量空间、子空间、线性映射）与其 Lean 表示（`Module`、`Submodule`、`LinearMap`）之间的对应关系。

---

### S01: Vector Spaces

**讲授内容：**
- `Module K V` 类型类（域上的向量空间或环上的模）。
- 向量空间公理：`smul_add`、`add_smul`、`smul_comm`。
- 线性映射 `V →[K] W`（`LinearMap K V W`）。
- 线性映射的复合、加法、数乘。
- `LinearMap.lsmul`：标量乘法作为线性映射。
- 线性等价 `V ≃ₗ[K] W`。
- 积和余积的泛性质。
- 直和 `⨁ V_i` 和直积 `Π V_i`。

**重要结论：**
- 积 `V × W` 满足向量空间范畴中积和余积的泛性质。
- 对有限索引类型，`⨁ V_i ≃ Π V_i`。

**注意要点：**
- `∘ₗ` 记号用于线性映射复合。
- 构造线性映射：`{ toFun := ..., map_add' := ..., map_smul' := ... }`。

---

### S02: Subspaces

**讲授内容：**
- `Submodule K V`：对 `add_mem` 和 `smul_mem` 封闭的子集。
- 子空间作为模块。
- `H ⊓ H'`（交）和 `H ⊔ H'`（和）。
- `IsCompl U V`：互补子空间。
- `DirectSum.IsInternal`：内部直和分解。
- `Submodule.span`：生成子空间。
- `span_induction` 归纳原理。
- `Submodule.map` 和 `Submodule.comap`。
- `LinearMap.range`、`LinearMap.ker`。
- 商空间 `V ⧸ E`。
- 对应定理。

**重要结论：**
- 单射 ⇔ `ker = ⊥`；满射 ⇔ `range = ⊤`。
- `(V / ker φ) ≃ range φ`（第一同构定理）。

**注意要点：**
- `span_induction` 用于证明生成空间中元素的性质。
- 子空间对 `Submodule.map` 和 `Submodule.comap` 是函子性的。

---

### S03: Endomorphisms

**讲授内容：**
- `End K V` = `V →[K] V`，乘法为复合。
- `aeval φ P`：多项式在自同态上的求值。
- 互素多项式的核分解（Fitting 分解）。
- 特征值和特征空间。
- 极小多项式。
- **Cayley-Hamilton 定理**。

**重要结论：**
- 若 `P` 和 `Q` 互素，则 `ker P(φ) ∩ ker Q(φ) = ⊥` 且 `ker P(φ) + ker Q(φ) = ker (P*Q)(φ)`。
- 特征值是极小多项式的根。
- **Cayley-Hamilton**：`aeval φ φ.charpoly = 0`。

**注意要点：**
- `IsCoprime P Q` 是核分解的假设。
- `Submodule` 的格运算（`⊓`、`⊔`）用于核。

---

### S04: Bases

**讲授内容：**
- 矩阵计算：加法、乘法、矩阵-向量作用、行列式、迹、转置、逆。
- `Basis ι K V`：`B i` 是基向量，`B.repr` 是同构 `V ≃ (ι →₀ K)`。
- 从线性无关生成族构造基：`Basis.mk`。
- `B.constr`：构造由基上的值唯一确定的线性映射。
- `toMatrix`：`(V →[K] W) ≃ Matrix ι' ι K`。
- 行列式与基无关。
- `Module.finrank K V`（有限维数）。
- Grassmann 关系。

**重要结论：**
- `finrank K (Fin n → K) = n`。
- `finrank ℝ ℂ = 2`。
- 行列式是基无关的。
- **Grassmann 关系**：`finrank (E ⊔ F) + finrank (E ⊓ F) = finrank E + finrank F`。

**注意要点：**
- `simp` 和 `norm_num` 用于矩阵代数。
- `Finsupp` 是有有限支撑的函数，作为模型空间。
- `toMatrix` 是线性等价。
- `Module.finrank`（自然数）vs `Module.rank`（基数）。

---

# 第11章：拓扑学（C11_Topology）

## 章节概述

本章涵盖从滤子到度量空间再到一般拓扑空间的拓扑学。介绍 Mathlib 通过滤子作为统一基础来表达拓扑的方法。

---

### S01: Filters

**讲授内容：**
- 滤子定义：向上封闭、包含 `univ`、在有限交下封闭的集族。
- 主滤子 `principal s`。
- `atTop` 滤子（Fréchet 滤子）。
- `Tendsto₁` vs `Tendsto₂` 的等价定义。
- `Filter.map` 和 `Filter.comap`。
- 积滤子。
- 滤子基 `HasBasis`。
- `∀ᶠ` 记号（"最终" / "几乎处处"）。
- `filter_upwards` 策略。

**重要结论：**
- 滤子方法统一了所有极限概念。
- `Tendsto` 的两种定义等价。
- 通过 `HasBasis` 获得具体的 ε-N/δ 特性。

**注意要点：**
- `∀ᶠ n in atTop, P n` 表示"对充分大的 n，P n 成立"。
- `filter_upwards` 是组合 `∀ᶠ` 假设的惯用方法。
- `𝓝 x` 是邻域滤子。

---

### S02: Metric Spaces

**讲授内容：**
- 度量空间公理：`dist_nonneg`、`dist_eq_zero`、`dist_comm`、`dist_triangle`。
- `EMetricSpace`、`PseudoMetricSpace` 等推广。
- 收敛和连续的 ε-δ 特性。
- 度量球：`Metric.ball`、`Metric.closedBall`。
- 开集和闭集。
- 紧致性：`isCompact_Icc`。
- Bolzano-Weierstrass、极值定理。
- 一致连续性。
- Cauchy 序列和完备性。
- **Baire 范畴定理**。

**重要结论：**
- 紧致集在连续函数下的像是紧致的。
- 紧致集上的连续函数一致连续。
- 完备度量空间是 Baire 空间：可数个稠密开集的交仍稠密。

**注意要点：**
- `Metric.nhds_basis_ball` 提供邻域球基。
- `choose!` 用于 Baire 定理证明中的依值选择。
- 紧致性在度量空间中等价于列紧。

---

### S03: Topological Spaces

**讲授内容：**
- 拓扑空间公理。
- 连续性的开集定义和滤子定义。
- 邻域滤子 `𝓝 x`。
- 诱导和余诱导拓扑。
- 积拓扑。
- 分离公理：`T2Space`（Hausdorff）、`RegularSpace`、`T3Space`。
- 第一可数拓扑和序列极限。
- 聚点 `ClusterPt`。
- 紧致性的滤子刻画。
- 紧致集的有限覆盖性质。

**重要结论：**
- 邻域滤子 `𝓝 x` 捕获整个拓扑。
- 诱导/余诱导拓扑通过伴随性与连续性相关联。
- Hausdorff 空间中极限唯一。
- 紧致性有多种等价表述（有限覆盖、滤子/超滤子、第一可数中的序列紧）。

**注意要点：**
- `continuous_iff_coinduced_le` 将连续性与诱导/余诱导伴随性关联。
- 滤子基础的紧致性定义是最一般的。
- 分离公理是泛函分析和代数拓扑的基础。

---

# 第12章：微分学（C12_Differential_Calculus）

## 章节概述

本章涵盖从单变量实分析到赋范空间中 Fréchet 导数的微分学。强调 Mathlib 中的导数 API：`HasDerivAt`、`HasFDerivAt`、`HasStrictFDerivAt` 和渐近记号 `IsBigO`/`IsLittleO`。

---

### S01: Elementary Differential Calculus

**讲授内容：**
- `HasDerivAt f f' x`：f 在 x 处有导数 f'。
- `hasDerivAt_sin 0`：sin 在 0 处的导数是 1。
- `DifferentiableAt ℝ f x`。
- `h.deriv`：`deriv f x = a`。
- 导数的线性：`deriv_add`。
- 局部极值的导数。
- **Rolle 定理**和**中值定理（MVT）**。
- 符号微分：`deriv (fun x ↦ x^5) 6 = 5 * 6^4`。

**重要结论：**
- **Rolle 定理**：`exists_deriv_eq_zero`。
- **中值定理**：`exists_deriv_eq_slope`。
- `simp` 知道许多标准导数。

**注意要点：**
- `HasDerivAt` → `deriv` 的关系通过 `h.deriv`。
- `simpa` 结合已知结果和简化。

---

### S02: Differential Calculus in Normed Spaces

**讲授内容：**
- 范数公理。
- 赋范群自动是度量空间。
- `NormedSpace ℝ E`。
- 有限维赋范空间是完备的。
- 连续线性映射 `E →L[𝕜] F`。
- 算子范数 `‖f‖` 和 `f.le_opNorm x`。
- **Banach-Steinhaus**（一致有界原理）。
- 渐近记号：`IsBigO`、`IsLittleO`。
- **Fréchet 导数**：`HasFDerivAt`。
- 高阶导数：`iteratedFDeriv`、`ContDiff`。
- **反函数定理**。

**重要结论：**
- **Banach-Steinhaus**：若逐点有界则一致有界（使用 Baire 定理）。
- **反函数定理**：`HasStrictFDerivAt.localInverse`。
- 局部逆可微，导数为 `(f')⁻¹`。

**注意要点：**
- `IsLittleO` 刻画 Fréchet 导数是关键概念定义。
- `ContinuousLinearMap`（`E →L[𝕜] F`）打包线性性和连续性。
- `calc` 块和 `filter_upwards` 用于渐近估计。

---

# 第13章：积分与测度论（C13_Integration_and_Measure_Theory）

## 章节概述

本章涵盖从一维 Riemann/区间积分到抽象测度论和 Lebesgue 积分的积分理论。介绍区间积分、微积分基本定理、测度、可测集、几乎处处概念和 Lebesgue 积分。

---

### S01: Elementary Integration

**讲授内容：**
- 区间积分：`∫ x in a..b, f x`。
- `[[a, b]]` 记号：从 `min a b` 到 `max a b` 的线段。
- `integral_id`：`∫ x in a..b, x = (b² - a²)/2`。
- `integral_one_div`：`∫ 1/x = log(b/a)`。
- **微积分第一基本定理**。
- **微积分第二基本定理**。
- 卷积：`(f ⋆ g)(x) = ∫ t, f t * g (x - t) dt`。

**重要结论：**
- 导数 `F(u) = ∫_a^u f(x) dx` 在 `b` 处为 `f(b)`。
- 若 `F' = f` 且 f 可积，则 `∫_a^b f = F(b) - F(a)`。

**注意要点：**
- `IntervalIntegrable` 类型类。
- `[[a, b]]` 记号用于有向线段。

---

### S02: Measure Theory

**讲授内容：**
- `MeasurableSpace` 和 `MeasurableSet`。
- 可数并/交需要 `Encodable ι`。
- `Measure α` 类型。
- 外正则性：`measure_eq_iInf s`。
- 可数次可加性。
- 可数可加性（对不交可测集）。
- `∀ᵐ` 记号（几乎处处）。

**重要结论：**
- 测度是可测集上的可数可加函数。
- `∀ᵐ` 通过 `ae` 滤子内化"几乎处处"。

**注意要点：**
- `Encodable` 对"可数"足够。
- `ae μ` 滤子方法使 `∀ᵐ` 与拓扑中的 `∀ᶠ` 记号兼容。

---

### S03: Integration

**讲授内容：**
- `Integrable` 类型类。
- 积分的线性性。
- `setIntegral_const c`。
- **控制收敛定理（DCT）**。
- **Fubini 定理**。
- 测度论意义下的卷积。
- **变量替换公式 / Jacobian 公式**。

**重要结论：**
- **DCT**：若 `F n` 可测、被可积函数界住、几乎处处收敛到 `f`，则 `∫ F n → ∫ f`。
- **Fubini**：`integral_prod f hf` 用于积测度。
- **变量替换**：`∫_{f(s)} g = ∫_s |det f'| * (g ∘ f)`（对微分同胚）。

**注意要点：**
- `AEStronglyMeasurable` 用于几乎处处可测函数。
- `SigmaFinite` 是 Fubini 的假设。
- `μ.IsAddHaarMeasure` 用于 Haar 测度（Jacobian 公式中使用）。
- Lebesgue/Bochner 积分满足线性、DCT、Fubini 和变量替换。

---

# 附录：重要策略和命令速查表

| 策略/命令 | 用途 | 首次出现 |
|---|---|---|
| `#eval` | 求值表达式 | C01/S01 |
| `#check` | 检查类型 | C01/S02 |
| `#print` | 打印定义 | C01/S02 |
| `rfl` | 自反性证明 | C01/S02 |
| `rw` | 重写等式 | C02/S01 |
| `calc` | 链式计算 | C02/S01 |
| `ring` | 环代数自动化 | C02/S01 |
| `nth_rw` | 重写特定位置 | C02/S01 |
| `linarith` | 线性算术自动化 | C02/S03 |
| `intro` | 引入假设/变量 | C03/S01 |
| `apply` | 使用引理结论 | C02/S03 |
| `exact` | 精确证明 | C02/S03 |
| `refine` | 带洞精确证明 | C02/S03 |
| `use` | 提供存在性见证 | C03/S02 |
| `rcases` | 解构假设 | C03/S02 |
| `rintro` | `intro` + `rcases` | C03/S02 |
| `have` | 创建辅助事实 | C02/S05 |
| `by_contra` | 反证法 | C03/S03 |
| `push_neg` | 推入否定 | C03/S03 |
| `contrapose!` | 逆否命题转换 | C03/S03 |
| `exfalso` | 变为 False | C03/S03 |
| `constructor` | 拆分合取目标 | C03/S04 |
| `left`/`right` | 选择析取侧 | C03/S05 |
| `by_cases` | 经典情况分析 | C03/S05 |
| `ext` | 外延性 | C04/S01 |
| `induction'` | 归纳法 | C05/S02 |
| `Finset.induction_on` | Finset 归纳 | C06/S01 |
| `structure` | 定义结构体 | C07/S01 |
| `class` | 定义类型类 | C07/S02 |
| `extends` | 类层级构建 | C08/S01 |
| `@[to_additive]` | 生成加法版本 | C08/S01 |
| `simp` | 简化 | 全课程 |
| `dsimp` | 定义简化 | C07/S01 |
| `gcongr` | 单调性链接 | C07/S03 |
| `field_simp` | 域表达式简化 | C07/S01 |
| `norm_num` | 数值计算 | C02/S02 |
| `group` | 群论恒等式 | C09/S01 |
| `abel` | 交换群恒等式 | C09/S01 |
| `filter_upwards` | 组合 `∀ᶠ` 假设 | C11/S01 |
| `omega` | 线性自然数算术 | C06/S03 |
| `choose!` | 依值选择 | C11/S02 |

---

> 本指南基于 MIL（Mathematics in Lean）课程内容整理，涵盖了 C01 到 C13 共 13 章的完整内容。
