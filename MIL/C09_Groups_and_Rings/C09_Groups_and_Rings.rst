.. _groups_and_ring:

群与环
======

我们在 :numref:`proving_identities_in_algebraic_structures` 中看到了如何在群和环中
进行运算推理。之后，在 :numref:`section_algebraic_structures` 中，我们看到了如何
定义抽象代数结构（如群结构），以及具体实例
（如高斯整数上的环结构）。:numref:`第 %s 章 <hierarchies>` 解释了
Mathlib 中如何处理抽象结构的层级。

在本章中，我们将更详细地讨论群和环。我们无法
涵盖 Mathlib 中这些主题的所有方面，尤其是因为 Mathlib 在不断发展。
但我们将提供库的入口点，并展示如何使用基本概念。
与 :numref:`第 %s 章 <hierarchies>` 的讨论有一些重叠，
但这里我们将重点放在如何使用 Mathlib 而非
这些主题处理方式背后的设计决策。
因此，理解某些例子可能需要回顾
:numref:`第 %s 章 <hierarchies>` 中的背景知识。
