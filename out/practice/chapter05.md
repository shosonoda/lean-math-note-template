# Chapter 05: 積分

Mathlib における基本的な測度と積分を扱います．

* Mathematics in Lean, 13. Integration and Measure Theory: <https://leanprover-community.github.io/mathematics_in_lean/C13_Integration_and_Measure_Theory.html>

区間積分，測度論，Bochner 積分，優収束定理，Fubini の定理などが概観されています．

Mathlib の積分はかなり一般的です．
実数値関数だけでなく，Banach 空間値の Bochner 積分を基本としており，測度は `Measure α`，値は拡張非負実数 `ℝ≥0∞` を使います．

```lean
import Mathlib

namespace PracticeChapter05

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval
```

---
## 測度空間と可測集合

可測空間構造は `MeasurableSpace α` です．
測度は `Measure α` で，可測集合だけでなく任意の集合 `s : Set α` に対して `μ s : ℝ≥0∞` が定義されています．
ただし，多くの定理では可測性の仮定が必要です．

```lean
#check MeasurableSpace
#check Measure
#check MeasurableSet
#check (fun {α : Type*} [MeasurableSpace α] => Measure α)

section MeasurableSets

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) := by
  exact MeasurableSet.empty

example : MeasurableSet (univ : Set α) := by
  exact MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet sᶜ := by
  exact hs.compl

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋃ i, f i) := by
  exact MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋂ i, f i) := by
  exact MeasurableSet.iInter h

end MeasurableSets
```

可算和や可算共通部分には，添字型が可算であることが必要です．
上の例では `[Encodable ι]` によって，`ι` が可算に符号化できることを仮定しています．

---
## 測度

測度 `μ : Measure α` は集合に `ℝ≥0∞` の値を割り当てます．
`ℝ≥0∞` は拡張非負実数で，無限大 `∞` を含みます．

```lean
#check ENNReal
#check (∞ : ℝ≥0∞)
#check MeasureTheory.Measure
#check measure_iUnion_le

section Measures

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t := by
  exact measure_eq_iInf s

example {ι : Type*} [Encodable ι] (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑' i, μ (s i) := by
  exact measure_iUnion_le s

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x := by
  rfl

end Measures
```

`∀ᵐ x ∂μ, P x` は「`μ` に関してほとんど至る所 `P x` が成り立つ」という意味です．
これはフィルター `ae μ` による `Eventually` の記法です．

---
## Bochner 積分

Mathlib の標準的な積分 `∫ x, f x ∂μ` は Bochner 積分です．
値域は実数だけでなく，完備なノルム空間に一般化されています．
多くの定理では `Integrable f μ` という仮定を使います．

```lean
#check Integrable
#check integral_add
#check setIntegral_const

section BochnerIntegral

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  exact integral_add hf hg

example {s : Set α} (c : E) : ∫ _ in s, c ∂μ = (μ s).toReal • c := by
  exact setIntegral_const c

end BochnerIntegral
```

定数関数の積分では，測度値 `μ s : ℝ≥0∞` を実数に戻すために `(μ s).toReal` が現れます．
`μ s = ∞` の場合には，非零定数関数は可積分でなく，積分は定義上 0 になるという規約とも整合しています．

---
## 区間積分

実数直線上の区間積分は `∫ x in a..b, f x` と書きます．
これは向きつきの区間積分で，`a` から `b` へ積分します．

```lean
#check intervalIntegral.integral_of_le
#check intervalIntegral.integral_hasStrictDerivAt_right

section IntervalIntegral

example : ∫ _ : ℝ in (0)..(1), (1 : ℝ) = 1 := by
  norm_num

example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b := by
  exact (intervalIntegral.integral_hasStrictDerivAt_right
    (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt).hasDerivAt.deriv

end IntervalIntegral
```

上の例は微分積分学の基本定理の一方向です．
積分を上端 `u` の関数と見たとき，その導関数が被積分関数 `f` になることを述べています．

---
## 収束定理と Fubini の定理

測度論の大きな定理も Mathlib に登録されています．
最初は全文を展開するより，定理名と型を確認して使うのが現実的です．

```lean
#check tendsto_integral_of_dominated_convergence
#check integral_prod
#check integral_image_eq_integral_abs_det_fderiv_smul

section Fubini

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [SigmaFinite μ] [SigmaFinite ν]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

example (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  exact integral_prod f hf

end Fubini
```

---
## 長めの例: 区間積分の具体計算

区間積分は，初等解析の例では `norm_num` や `ring_nf` と連携して計算できることがあります．
まずは定数関数と恒等関数の積分を見ます．

```lean
section ConcreteIntervalIntegrals

example : ∫ _ : ℝ in (0)..(2), (3 : ℝ) = 6 := by
  norm_num

example : ∫ x : ℝ in (0)..(1), x = (1 / 2 : ℝ) := by
  norm_num

example : ∫ x : ℝ in (0)..(2), x = (2 : ℝ) := by
  norm_num

end ConcreteIntervalIntegrals
```

これらの例は，内部では区間積分に関する既存定理と実数計算を使っています．
複雑な被積分関数では `norm_num` だけで閉じないことも多く，
その場合は微分積分学の基本定理や積分の線形性を明示的に使います．

---
## 長めの例: 区間積分の線形性

積分の線形性は，関数の可積分性を仮定して使います．
区間積分では `IntervalIntegrable f volume a b` がよく現れます．

```lean
section LinearityOfIntervalIntegral

example {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x : ℝ in a..b, f x + g x =
      (∫ x : ℝ in a..b, f x) + ∫ x : ℝ in a..b, g x := by
  exact intervalIntegral.integral_add hf hg

example (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x : ℝ in a..b, c * f x = c * ∫ x : ℝ in a..b, f x := by
  exact intervalIntegral.integral_const_mul c f

end LinearityOfIntervalIntegral
```

紙の数学では，積分の線形性はほとんど自明に使います．
Lean では，被積分関数が適切に積分可能であることが theorem の仮定に現れます．
定数倍については theorem が仮定なしの形で使えることもありますが，これは積分が定義上全関数に拡張されているためです．
本格的な解析では，可積分性の仮定を明示して使うのが安全です．

---
## まとめ

積分の章では，`MeasurableSpace`，`Measure`，`MeasurableSet`，`Integrable`，`∫` 記法，`∀ᵐ` 記法を読むことが第一歩です．
実数値積分だけを見ている場合でも，Mathlib の内部では Bochner 積分と測度論の一般的な枠組みが使われます．

したがって，積分の証明では，可測性，可積分性，完備性，σ有限性などの仮定がどこで必要になるかを `#check` で確認しながら進めるのが重要です．

### 形式化の tips

積分の形式化では，計算そのものよりも仮定の整理が難しいことが多いです．

1. 可測集合かどうかは `MeasurableSet`．
2. 関数の可測性は `Measurable` や `AEStronglyMeasurable`．
3. 積分可能性は `Integrable`．
4. ほとんど至る所は `∀ᵐ x ∂μ, ...`．
5. 区間積分では `IntervalIntegrable f volume a b`．
6. 直積測度や Fubini では `SigmaFinite` または `SFinite` 仮定を確認する．

---
## 演習問題

1. 定数関数の区間積分を計算してください．

    ```lean4
    example : ∫ _ : ℝ in (1)..(4), (2 : ℝ) = 6 := by
      -- `norm_num` を試す．
      sorry
    ```

2. 積分の和に関する線形性を `intervalIntegral.integral_add` で証明してください．

    ```lean4
    example {f g : ℝ → ℝ} {a b : ℝ}
        (hf : IntervalIntegrable f volume a b)
        (hg : IntervalIntegrable g volume a b) :
        ∫ x : ℝ in a..b, f x + g x =
          (∫ x : ℝ in a..b, f x) + ∫ x : ℝ in a..b, g x := by
      -- ヒント: `exact intervalIntegral.integral_add hf hg`
      sorry
    ```

3. 可測集合の補集合が可測であることを示してください．

    ```lean4
    example {α : Type*} [MeasurableSpace α] {s : Set α}
        (hs : MeasurableSet s) : MeasurableSet sᶜ := by
      -- ヒント: `exact hs.compl`
      sorry
    ```

4. ほとんど至る所の記法 `∀ᵐ` が filter の `Eventually` であることを確認してください．

    ```lean4
    example {α : Type*} [MeasurableSpace α] {μ : Measure α} {P : α → Prop} :
        (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x := by
      -- ヒント: `rfl`
      sorry
    ```

5. Bochner 積分の加法性を使ってください．

    ```lean4
    example {α E : Type*} [MeasurableSpace α]
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        {μ : Measure α} {f g : α → E}
        (hf : Integrable f μ) (hg : Integrable g μ) :
        ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
      -- ヒント: `exact integral_add hf hg`
      sorry
    ```

6. Fubini の定理の statement を `#check` で読み，どこに `SigmaFinite` 仮定が現れるか確認してください．

    ```lean4
    #check integral_prod
    ```

7. 区間の向きを反転したときの積分を調べてください．

    ```lean4
    #check intervalIntegral.integral_symm
    ```

8. `∫ x in a..b, f x` と `∫ x in b..a, f x` の関係を使って，定数関数の例を逆向き区間で計算してください．

    ```lean4
    example : ∫ _ : ℝ in (2)..(0), (3 : ℝ) = -6 := by
      -- `norm_num` を試す．
      sorry
    ```

9. `MeasurableSet.iUnion` の仮定を読み，可算性がどこで必要か確認してください．

    ```lean4
    #check MeasurableSet.iUnion
    ```

10. 優収束定理の statement を読み，どの仮定が「支配関数」に対応するか確認してください．

    ```lean4
    #check tendsto_integral_of_dominated_convergence
    ```
