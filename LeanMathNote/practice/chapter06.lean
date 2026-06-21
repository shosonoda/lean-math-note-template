--#--
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
--#--
/-
# Chapter 06: 確率論

Mathlib における基本的な確率論を概観します．

参考:

* Basic probability in Mathlib: <https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/>
* Rémy Degenne, Markov kernels in Mathlib's probability library: <https://arxiv.org/abs/2510.04070>

前章の測度論・積分の上に，確率測度，事象，確率変数，期待値，独立性，条件付き確率，Markov kernel が定義されています．

確率論の形式化では，紙の数学で「確率空間」と一言で済ませる部分を，Lean ではいくつかの型と型クラスに分けて書きます．
典型的には，標本空間は型 `Ω`，可測構造は `[MeasurableSpace Ω]`，確率測度は `P : Measure Ω` と `[IsProbabilityMeasure P]` です．
-/
import Mathlib
set_option linter.missingDocs false --#
namespace PracticeChapter06

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

/-
---
## 確率空間と確率測度

Mathlib では，測度論の `Measure Ω` をそのまま使い，確率測度であることを型クラス `IsProbabilityMeasure P` で表します．
定義上，`IsProbabilityMeasure P` は `P univ = 1` を主張する命題です．
ここで `P s` の値は `ℝ≥0∞`，つまり拡張非負実数です．
確率測度の場合は全体の測度が `1` なので，各事象の確率は `∞` にはなりません．
-/

#check Measure
#check IsProbabilityMeasure
#check ProbabilityMeasure
#check measure_univ
#check measure_ne_top
#check measure_lt_top

section ProbabilitySpaces

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

example : P univ = 1 := by
  simp

example (s : Set Ω) : P s ≤ 1 := by
  exact prob_le_one

example (s : Set Ω) : P s ≠ ∞ := by
  simp

example (s : Set Ω) : P s < ∞ := by
  simp

example (s : Set Ω) : ℝ≥0∞ :=
  P s

end ProbabilitySpaces

/-
`ProbabilityMeasure Ω` という型もあります．
これは確率測度を subtype として束ねた型で，確率測度全体の空間や弱収束などを扱うときに使われます．
普通の定理を書くときは，`P : Measure Ω` と `[IsProbabilityMeasure P]` を仮定する形の方が，既存の測度論ライブラリと合わせやすいです．

標本空間に標準の測度を持たせたい場合は `[MeasureSpace Ω]` を使います．
この標準測度は `volume` で，確率論のスコープを開くと `ℙ` と書けます．
ただし，`ℙ` が確率測度であることは別に `[IsProbabilityMeasure (ℙ : Measure Ω)]` と仮定します．
-/

section CanonicalMeasure

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

example : (ℙ : Measure Ω) univ = 1 := by
  simp

example (s : Set Ω) : (ℙ : Measure Ω) s ≤ 1 := by
  exact prob_le_one

end CanonicalMeasure

/-
---
## 事象と条件付き確率

Mathlib に「事象」という専用の型はありません．
事象は `s : Set Ω` として表し，多くの定理では `MeasurableSet s` を仮定します．
確率は単に測度の適用 `P s` です．

条件付き確率は `P[s | t]` と書けます．
これは条件付き測度 `P[|t]` を事象 `s` に適用したものです．
定義を展開すると，条件にしている集合 `t` が可測であるとき，
`P[s | t] = (P t)⁻¹ * P (t ∩ s)` になります．
分母が 0 の場合も，`ℝ≥0∞` の逆元を使った全域的な定義として扱われます．
-/

section Events

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω}
variable {s t : Set Ω}

#check MeasurableSet
#check ProbabilityTheory.cond
#check (P[|t])
#check (P[s | t])

example : P[s | t] = P[|t] s := by
  rfl

example (ht : MeasurableSet t) : P[s | t] = (P t)⁻¹ * P (t ∩ s) := by
  rw [cond_apply ht]

end Events

/-
---
## 確率変数，分布，期待値

確率変数は，測度空間から可測空間への可測関数です．
Lean では関数 `X : Ω → E` と可測性の仮定 `hX : Measurable X` を分けて持ちます．
確率変数 `X` の分布は，測度の push-forward `P.map X` です．
期待値は積分で，`∫ ω, X ω ∂P` と書けます．
確率論スコープでは `P[X]` という記法も使えます．
-/

section RandomVariables

variable {Ω E : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace E]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X Y : Ω → E}

#check Measurable
#check Measure.map
#check (P.map X)
#check (fun X : Ω → ℝ => P[X])

example {X : Ω → E} (hX : AEMeasurable X P) : IsProbabilityMeasure (P.map X) := by
  exact Measure.isProbabilityMeasure_map hX

example (c : E) : ∫ _ : Ω, c ∂P = c := by
  simp

example {X Y : Ω → E} (hX : Integrable X P) (hY : Integrable Y P) :
    ∫ ω, X ω + Y ω ∂P = ∫ ω, X ω ∂P + ∫ ω, Y ω ∂P := by
  exact integral_add hX hY

end RandomVariables

/-
`P[X]` は Bochner 積分の記法です．
したがって値域 `E` にはノルム空間の構造が必要です．
`ℝ≥0∞` 値の非負関数を積分するときは，前章で見た Lebesgue 積分 `∫⁻` を使います．
この点は紙の確率論では同じ「期待値」と呼ばれがちですが，Mathlib では型によって使う積分が分かれます．
-/

/-
---
## 離散確率と `PMF`

離散確率では，可測性が問題にならないことが多いです．
Mathlib では `[DiscreteMeasurableSpace Ω]` が「すべての集合が可測である」ことを表します．
その場合，任意の関数 `X : Ω → E` は可測関数になります．

確率質量関数は `PMF Ω` で表されます．
`p : PMF Ω` から測度 `p.toMeasure : Measure Ω` を作ることができ，これは確率測度です．
有限集合上の一様分布や Bernoulli 分布も `PMF` として用意されています．
-/

section DiscreteProbability

variable {Ω E : Type*}
variable [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
variable [MeasurableSpace E]

#check DiscreteMeasurableSpace
#check MeasurableSet.of_discrete
#check Measurable.of_discrete
#check PMF
#check PMF.toMeasure
#check PMF.uniformOfFintype
#check PMF.bernoulli

example (s : Set Ω) : MeasurableSet s := by
  exact MeasurableSet.of_discrete

example (X : Ω → E) : Measurable X := by
  exact Measurable.of_discrete

example (p : PMF Ω) : IsProbabilityMeasure p.toMeasure := by
  infer_instance

example (p : PMF Ω) : p.toMeasure univ = 1 := by
  simp

end DiscreteProbability

/-
---
## 独立性と同分布

独立性も，関数・集合・可測空間に対してそれぞれ定義されています．
確率変数 `X : Ω → E` と `Y : Ω → F` の独立性は `IndepFun X Y P` と書きます．
集合の独立性は `IndepSet s t P`，族の独立性は `iIndepFun` や `iIndepSet` です．
同分布は `IdentDistrib X Y P Q` で表します．

まずは定義を展開して使うより，定理の仮定に現れる型を読めることが重要です．
-/

section Independence

variable {Ω E F : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
variable {P : Measure Ω}
variable {X : Ω → E} {Y : Ω → F}

#check IndepFun
#check iIndepFun
#check IndepSet
#check iIndepSet
#check IdentDistrib

example (h : IndepFun X Y P) : IndepFun Y X P := by
  exact h.symm

end Independence

/-
---
## Markov kernel

Markov kernel は，状態 `a : α` ごとに測度 `κ a : Measure β` を返す可測な写像です．
Mathlib では `Kernel α β` が kernel を表し，その各値が確率測度であることを `IsMarkovKernel κ` で表します．

参照論文では，Mathlib の確率論ライブラリが Markov kernel を広く使っていることが説明されています．
条件付き分布，posterior distribution，独立性・条件付き独立性の統一的な定義，sub-Gaussian random variables，entropy，Kullback-Leibler divergence などで kernel が中心的な役割を持ちます．
この章では入口だけを見ます．
-/

section MarkovKernels

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]

#check Kernel
#check IsMarkovKernel
#check IsFiniteKernel
#check IsSFiniteKernel
#check Kernel.measurable
#check Kernel.bound
#check Kernel.deterministic
#check condDistrib

example (κ : Kernel α β) : Measurable κ := by
  exact κ.measurable

example (κ : Kernel α β) [IsMarkovKernel κ] (a : α) : κ a univ = 1 := by
  simp

example : IsFiniteKernel (0 : Kernel α β) := by
  infer_instance

variable {f : α → β} (hf : Measurable f)

example : IsMarkovKernel (Kernel.deterministic f hf) := by
  infer_instance

example (a : α) : Kernel.deterministic f hf a = Measure.dirac (f a) := by
  exact Kernel.deterministic_apply hf a

end MarkovKernels

/-
---
## まとめ

Mathlib の確率論は，測度論の上に構築されています．
確率空間は `Ω`，`MeasurableSpace Ω`，`P : Measure Ω`，`IsProbabilityMeasure P` に分けて読みます．
事象は `Set Ω`，確率変数は可測関数，分布は `P.map X`，期待値は積分です．

離散確率では `PMF` が便利ですが，定理としては `Measure` と `DiscreteMeasurableSpace` の形で書く方が既存ライブラリと接続しやすいことがあります．
条件付き確率や条件付き分布に進むと，Markov kernel が自然に現れます．
確率論の Mathlib コードを読むときは，確率論固有の用語と測度論の語彙がどの型で対応しているかを確認してください．
-/

/-
---
## 演習問題

1. 確率測度では全体の測度が 1 であることを確認してください．

    ```lean4
    example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
        P univ = 1 := by
      sorry
    ```

2. 条件付き確率の定義を展開してください．

    ```lean4
    example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {s t : Set Ω} (ht : MeasurableSet t) :
        P[s | t] = (P t)⁻¹ * P (t ∩ s) := by
      sorry
    ```

3. 定数確率変数の期待値を計算してください．

    ```lean4
    example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (c : ℝ) : ∫ _ : Ω, c ∂P = c := by
      sorry
    ```

4. 離散可測空間では任意の集合が可測であることを確認してください．

    ```lean4
    example {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
        (s : Set Ω) : MeasurableSet s := by
      sorry
    ```

5. `PMF` から作った測度が確率測度であることを確認してください．

    ```lean4
    example {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) :
        IsProbabilityMeasure p.toMeasure := by
      sorry
    ```

6. 独立性の対称性を使ってください．

    ```lean4
    example {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
        {P : Measure Ω} {X : Ω → E} {Y : Ω → F}
        (h : IndepFun X Y P) : IndepFun Y X P := by
      sorry
    ```

7. deterministic kernel が Dirac 測度を返すことを確認してください．

    ```lean4
    example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
        {f : α → β} (hf : Measurable f) (a : α) :
        Kernel.deterministic f hf a = Measure.dirac (f a) := by
      sorry
    ```
-/

--#--
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
    P univ = 1 := by
  sorry

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s t : Set Ω} (ht : MeasurableSet t) :
    P[s | t] = (P t)⁻¹ * P (t ∩ s) := by
  sorry

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (c : ℝ) : ∫ _ : Ω, c ∂P = c := by
  sorry

example {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (s : Set Ω) : MeasurableSet s := by
  sorry

example {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) :
    IsProbabilityMeasure p.toMeasure := by
  sorry

example {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} {X : Ω → E} {Y : Ω → F}
    (h : IndepFun X Y P) : IndepFun Y X P := by
  sorry

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) (a : α) :
    Kernel.deterministic f hf a = Measure.dirac (f a) := by
  sorry
--#--

end --#

end PracticeChapter06 --#
