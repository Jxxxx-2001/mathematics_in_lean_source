import Mathlib.Tactic

/- TEXT:
.. _inductively_defined_types:

归纳定义的类型
-------------------------

Lean 的基础允许我们定义归纳类型，即其实例
从底层向上生成的数据类型。
例如，类型 ``List α``（``α`` 的元素列表）是通过从空列表 ``nil`` 开始，
并逐步向列表前面添加元素来生成的。
下面我们将定义一个二叉树类型 ``BinTree``，其元素是通过
从空树开始，并通过将新节点附加到两棵现有树来构建新树而生成的。

在 Lean 中，人们可以定义对象为无限的归纳类型，比如可数分支的
良基树。
然而，有限归纳定义在离散数学中很常用，
特别是在那些与计算机科学相关的离散数学分支中。
Lean 不仅提供了定义此类类型的方法，还提供了
归纳原理和递归定义。例如，数据类型 ``List α`` 是归纳定义的：
EXAMPLES: -/
-- QUOTE:
namespace MyListSpace

inductive List (α : Type*) where
  | nil  : List α
  | cons : α → List α → List α

end MyListSpace
-- QUOTE.

/- TEXT:
归纳定义说明了 ``List α`` 的每个元素要么是 ``nil``（空列表），
要么是 ``cons a as``，其中 ``a`` 是 ``α`` 的一个元素，而 ``as`` 是 ``α`` 元素的列表。
构造子正式命名为 ``List.nil`` 和 ``List.cons``，但当你打开 ``List`` 命名空间时，
可以使用更短的记号。
当 ``List`` 命名空间*未*打开时，你可以在任何
Lean 期望列表的地方写出 ``.nil`` 和 ``.cons a as``，Lean 会自动插入 ``List`` 限定符。
在本节中，我们将把临时定义放在单独的命名空间中，如
``MyListSpace``，以避免与标准库冲突。在临时命名空间之外，
我们恢复使用标准库的定义。

Lean 为 ``nil`` 定义记号 ``[]``，为 ``cons`` 定义记号 ``::``，你可以
将 ``[a, b, c]`` 写为 ``a :: b :: c :: []``。追加和映射函数
递归定义如下：
EXAMPLES: -/
namespace MyListSpace2

-- QUOTE:
def append {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: (append as bs)

def map {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map f as

#eval append [1, 2, 3] [4, 5, 6]
#eval map (fun n => n^2) [1, 2, 3, 4, 5]
-- QUOTE.

/- TEXT:
请注意，这里有一个基本情况和一个递归情况。
在每种情况下，两个定义子句都按定义成立：
EXAMPLES: -/
-- QUOTE:
theorem nil_append {α : Type*} (as : List α) : append [] as = as := rfl

theorem cons_append {α : Type*} (a : α) (as : List α) (bs : List α) :
    append (a :: as) bs = a :: (append as bs) := rfl

theorem map_nil {α β : Type*} (f : α → β) : map f [] = [] := rfl

theorem map_cons {α β : Type*} (f : α → β) (a : α) (as : List α) :
    map f (a :: as) = f a :: map f as := rfl
-- QUOTE.

end MyListSpace2

/- TEXT:
函数 ``append`` 和 ``map`` 在标准库中有定义，``append as bs``
可以写作 ``as ++ bs``。

Lean 允许你按照定义的结构通过归纳来写证明。
BOTH: -/
namespace MyListSpace3

-- QUOTE:
variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

-- EXAMPLES:
theorem append_nil : ∀ as : List α, as ++ [] = as
  | [] => rfl
  | a :: as => by rw [cons_append, append_nil as]

theorem map_map (f : α → β) (g : β → γ) :
    ∀ as : List α, map g (map f as) = map (g ∘ f) as
  | [] => rfl
  | a :: as => by rw [map_cons, map_cons, map_cons, map_map f g as]; rfl
-- QUOTE.

/- TEXT:
你也可以使用 ``induction'`` 策略。

EXAMPLES: -/
theorem append_nil' : as ++ [] = as := by
  induction' as with a as ih
  . rfl
  . rw [cons_append, ih]

theorem map_map' (f : α → β) (g : β → γ) (as : List α) :
    map g (map f as) = map (g ∘ f) as := by
  induction' as with a as ih
  . rfl
  . simp [map, ih]

/- TEXT:
当然，这些定理已经在标准库中。作为练习，
尝试在 ``MyListSpace3`` 命名空间中定义一个函数 ``reverse``（以避免
与标准 ``List.reverse`` 冲突）来反转一个列表。
你可以使用 ``#eval reverse [1, 2, 3, 4, 5]`` 来测试它。
``reverse`` 的最直接定义
需要平方时间，但不用为此担心。
你可以跳转到标准库中 ``List.reverse`` 的定义来查看
线性时间实现。
尝试证明 ``reverse (as ++ bs) = reverse bs ++ reverse as`` 和
``reverse (reverse as) = as``。
你可以使用 ``cons_append`` 和 ``append_assoc``，但你
可能需要想出辅助引理并证明它们。
EXAMPLES: -/
-- QUOTE:
def reverseαα : List α → List α := sorry

theorem reverse_appendαα (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  sorry

theorem reverse_reverseαα (as : List α) : reverse (reverse as) = as := by sorry
-- QUOTE.
-- SOLUTIONS:
def reverse : List α → List α
  | []      => []
  | a :: as => reverse as ++ [a]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction' as with a as ih
  . rw [nil_append, reverse, append_nil]
  rw [cons_append, reverse, ih, reverse, append_assoc]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction' as with a as ih
  . rfl
  rw [reverse, reverse_append, ih, reverse, reverse, nil_append, cons_append, nil_append]
-- BOTH:

end MyListSpace3

/- TEXT:
另一个例子，考虑以下二叉树的归纳定义，以及
计算二叉树大小和深度的函数。
BOTH: -/
-- QUOTE:
inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree

namespace BinTree

def size : BinTree → ℕ
  | empty    => 0
  | node l r => size l + size r + 1

def depth : BinTree → ℕ
  | empty    => 0
  | node l r => max (depth l) (depth r) + 1
-- QUOTE.

/- TEXT:
将空二叉树计为大小为 0 深度为 0 的二叉树是方便的。
在文献中，这种数据类型有时被称为*扩展二叉树*。
包含空树意味着，例如，我们可以定义树
``node empty (node empty empty)``，它由一个根节点、一个空的左子树
和一个由单个节点组成的右子树构成。

这里有一个关于大小和深度的重要不等式：
EXAMPLES: -/
-- QUOTE:
theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | empty    => Nat.zero_le _
  | node l r => by
    simp only [depth, size]
    calc l.size + r.size + 1
      ≤ (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
          gcongr <;> apply size_le
    _ ≤ (2 ^ max l.depth r.depth - 1) + (2 ^ max l.depth r.depth - 1) + 1 := by
          gcongr <;> simp
    _ ≤ 2 ^ (max l.depth r.depth + 1) - 1 := by
          have : 0 < 2 ^ max l.depth r.depth := by simp
          omega
-- QUOTE.

/- TEXT:
尝试证明以下不等式，这个稍微容易一些。
记住，如果你像前一个定理那样通过归纳进行证明，
你必须删除 ``:= by``。
EXAMPLES: -/
-- QUOTE:
theorem depth_le_sizeαα : ∀ t : BinTree, depth t ≤ size t := by sorry
-- QUOTE.

-- SOLUTIONS:
theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t
  | BinTree.empty => Nat.zero_le _
  | BinTree.node l r => by
    simp only [depth, size, add_le_add_iff_right, max_le_iff]
    constructor
    . apply le_add_right
      apply depth_le_size
    . apply le_add_left
      apply depth_le_size

/- TEXT:
也请定义二叉树上的 ``flip`` 操作，它递归地交换
左右子树。
EXAMPLES: -/
-- QUOTE:
def flipαα : BinTree → BinTree := sorry
-- QUOTE.

/- TEXT:
如果你做得对，以下证明应该是 `rfl`。
EXAMPLES: -/
-- QUOTE:
example: flipαα  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := sorry
-- QUOTE.

/- TEXT:
证明以下命题：
EXAMPLES: -/
-- QUOTE:
theorem size_flipαα : ∀ t, size (flipαα t) = size t := by sorry
-- QUOTE.
-- SOLUTIONS:
def flip : BinTree → BinTree
  | empty => empty
  | node l r => node (flip r) (flip l)

example: flip  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := rfl

theorem size_flip : ∀ t, size (flip t) = size t
  | empty => rfl
  | node l r => by
      dsimp [size, flip]
      rw [size_flip l, size_flip r]; omega

-- BOTH:
end BinTree

/- TEXT:
我们以一些形式逻辑来结束本节。
以下是命题公式的归纳定义。
BOTH: -/
-- QUOTE:
inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm
-- QUOTE.
namespace PropForm

/- TEXT:
每个命题公式要么是一个变量 ``var n``，常量假 ``fls``，
要么是形如 ``conj A B``、``disj A B`` 或 ``impl A B`` 的复合公式。
用通常的数学记号，这些通常写作 :math:`p_n`、:math:`\bot`、:math:`A \wedge B`、
:math:`A \vee B` 和 :math:`A \to B`。
其他命题连接词可以用这些来定义；例如，我们可以
将 :math:`\neg A` 定义为 :math:`A \to \bot`，将 :math:`A \leftrightarrow B` 定义为
:math:`(A \to B) \wedge (B \to A)`。

定义了命题公式的数据类型之后，我们定义
命题公式相对于对变量的
布尔真值赋值 ``v`` 的求值意味着什么。
BOTH: -/
-- QUOTE:
def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v
-- QUOTE.

/- TEXT:
下一个定义指定了公式中出现的变量的集合，随后的
定理表明，在公式的变量上一致的两个真值赋值下求值公式
得到相同的值。
BOTH: -/
-- QUOTE:
def vars : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.vars ∪ B.vars
  | disj A B => A.vars ∪ B.vars
  | impl A B => A.vars ∪ B.vars

-- EXAMPLES:
theorem eval_eq_eval : ∀ (A : PropForm) (v1 v2 : ℕ → Bool),
    (∀ n ∈ A.vars, v1 n = v2 n) → A.eval v1 = A.eval v2
  | var n, v1, v2, h    => by simp_all [vars, eval]
  | fls, v1, v2, h      => by simp_all [eval]
  | conj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | disj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | impl A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
-- QUOTE.

/- TEXT:
注意到重复，我们可以巧妙地使用自动化。
EXAMPLES: -/
-- QUOTE:
theorem eval_eq_eval' (A : PropForm) (v1 v2 : ℕ → Bool) (h : ∀ n ∈ A.vars, v1 n = v2 n) :
    A.eval v1 = A.eval v2 := by
  cases A <;> simp_all [eval, vars, fun A => eval_eq_eval' A v1 v2]
-- QUOTE.

/- TEXT:
函数 ``subst A m C`` 描述了在公式 ``A`` 中将公式 ``C`` 替换
变量 ``var m`` 的每次出现的结果。
BOTH: -/
-- QUOTE:
def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)
-- QUOTE.

/- TEXT:
作为例子，证明对不出现在公式中的变量进行替换
没有效果：
EXAMPLES: -/
-- QUOTE:
theorem subst_eq_of_not_mem_varsαα :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.vars → A.subst n C = A := sorry
-- QUOTE.

-- SOLUTIONS:
theorem subst_eq_of_not_mem_vars :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.vars → A.subst n C = A
  | var m, n, C, h => by simp_all [subst, vars]; tauto
  | fls, n, C, _ => by rw [subst]
  | conj A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]
  | disj A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]
  | impl A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]

-- 替代证明：
theorem subst_eq_of_not_mem_vars' (A : PropForm) (n : ℕ) (C : PropForm):
    n ∉ A.vars → A.subst n C = A := by
  cases A <;> simp_all [subst, vars, subst_eq_of_not_mem_vars']; tauto

/- TEXT:
以下定理说明了一些更微妙和有趣的东西：
在真值赋值 ``v`` 下求值 ``A.subst n C`` 得到的值等同于
在将 ``C`` 的值赋予 ``var n`` 的真值赋值下求值 ``A`` 得到的值。
看看你能否证明它。
EXAMPLES: -/
-- QUOTE:
theorem subst_eval_eqαα : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := sorry
-- QUOTE.
-- SOLUTIONS:
theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m)
  | var m, n, C, v => by
    simp [subst, eval]
    split <;> simp [eval]
  | fls, n, C, v => by
    simp [subst, eval]
  | conj A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]
  | disj A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]
  | impl A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]

-- 替代证明：
theorem subst_eval_eq' (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool) :
    (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := by
  cases A <;> simp [subst, eval, subst_eval_eq'];
    split <;> simp_all [eval]
-- BOTH:

end PropForm
