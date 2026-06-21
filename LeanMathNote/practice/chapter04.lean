--#--
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
--#--
/-
# Chapter 04: 微分

Mathlib における基本的な微分を扱います．

参考:

* Mathematics in Lean, 12. Differential Calculus: <https://leanprover-community.github.io/mathematics_in_lean/C12_Differential_Calculus.html>

実数値関数の初等微分から，ノルム空間上の Fréchet 微分までが説明されています．

微分に関する主な述語・関数は次の通りです．

* `HasDerivAt f f' x`: 1 変数関数 `f` が点 `x` で微分係数 `f'` を持つ．
* `DifferentiableAt ℝ f x`: `f` が点 `x` で微分可能である．
* `deriv f x`: `f` の点 `x` における微分係数．微分不能な点では 0 と定義される．
* `HasFDerivAt f f' x`: ノルム空間上の Fréchet 微分．
* `fderiv 𝕜 f x`: Fréchet 微分としての導関数．
-/
import Mathlib
set_option linter.missingDocs false --#

namespace PracticeChapter04

noncomputable section

open Set Filter
open scoped Topology

/-
---
## Mathlib における微分の形式化

Mathlib の微分は，1 変数実関数の極限

```text
(f x' - f x) / (x' - x)
```

から直接始めるのではなく，ノルム空間上の **Fréchet 微分**を中心に実装されています．
基礎になる型は，ノルム体 `𝕜` 上のノルム空間 `E`，`F` と，関数 `f : E → F` です．
点 `x : E` における微分は数ではなく，連続線形写像 `f' : E →L[𝕜] F` として表されます．

数学的には，`HasFDerivAt f f' x` は

```text
f x' = f x + f' (x' - x) + o(x' - x)    as x' → x
```

という一次近似を表します．
Lean ではこの `o` はフィルター `𝓝 x` に沿った漸近記法として表されます．
Mathlib の定義ファイルでは，さらに一般に `HasFDerivAtFilter` が用意されており，
通常の点での微分 `HasFDerivAt`，集合内での微分 `HasFDerivWithinAt`，逆関数定理などで使う strict derivative `HasStrictFDerivAt` が，
どのフィルターに沿って同じ一次近似を見るかの違いとして定義されています．

`DifferentiableAt 𝕜 f x` は「そのような連続線形写像 `f'` が存在する」という述語です．
一方 `fderiv 𝕜 f x` は導関数を値として返す関数です．
導関数が存在すればその値を返し，存在しなければ 0 に定義されます．
そのため，証明ではまず `HasFDerivAt` や `HasDerivAt` を作り，最後に `.fderiv` や `.deriv` で値としての導関数へ移るのが安定です．

1 変数の `HasDerivAt f f' x` は，この Fréchet 微分の特殊化です．
関数 `f : 𝕜 → F` の微分係数 `f' : F` を，`h ↦ h • f'` という連続線形写像に対応させて `HasFDerivAt` に戻しています．
特に `f : ℝ → ℝ` なら，いつもの微分係数は実数として現れます．
`deriv f x` は `fderiv 𝕜 f x` を方向 `1` に評価したものです．

Mathematics in Lean Chapter 12 もこの構成に沿っており，前半では `HasDerivAt`，`deriv`，Rolle の定理や平均値の定理を扱い，
後半ではノルム空間，連続線形写像 `E →L[𝕜] F`，漸近記法 `=O`・`=o`，`HasFDerivAt`，`ContDiff`，逆関数定理へ進みます．
-/

#check HasFDerivAtFilter
#check HasFDerivAt
#check HasDerivAtFilter
#check HasDerivAt
#check fderiv
#check deriv

section DifferentialDefinitions

open Asymptotics

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example {f : E → F} {f' : E →L[𝕜] F} {x : E} :
    HasFDerivAt f f' x ↔
      (fun x' => f x' - f x - f' (x' - x)) =o[𝓝 x] (fun x' => x' - x) := by
  exact hasFDerivAt_iff_isLittleO

example {f : E → F} {f' : E →L[𝕜] F} {x : E} :
    HasFDerivAt f f' x ↔
      Filter.Tendsto
        (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖)
        (𝓝 x)
        (𝓝 0) := by
  exact hasFDerivAt_iff_tendsto

example {f : 𝕜 → F} {f' : F} {x : 𝕜} :
    HasDerivAt f f' x ↔
      (fun x' => f x' - f x - (x' - x) • f') =o[𝓝 x] (fun x' => x' - x) := by
  exact hasDerivAt_iff_isLittleO

example {f : 𝕜 → F} {x : 𝕜} : deriv f x = (fderiv 𝕜 f x) 1 := by
  rfl

end DifferentialDefinitions

/-
---
## 実数値関数の微分

実数から実数への関数では，点での微分係数を `HasDerivAt` で表します．
微分係数を明示しない場合は `DifferentiableAt ℝ` を使います．
-/

#check HasDerivAt
#check DifferentiableAt
#check deriv

section RealDerivatives

open Real

example : HasDerivAt sin 1 0 := by
  simpa using hasDerivAt_sin 0

example (x : ℝ) : DifferentiableAt ℝ sin x := by
  exact (hasDerivAt_sin x).differentiableAt

example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a := by
  exact h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬ DifferentiableAt ℝ f x) : deriv f x = 0 := by
  exact deriv_zero_of_not_differentiableAt h

example : deriv (fun x : ℝ => x ^ 5) 6 = 5 * 6 ^ 4 := by
  simp

example : deriv sin π = -1 := by
  simp

end RealDerivatives

/-
`deriv f x` は，任意の関数 `f : ℝ → ℝ` と点 `x` に対して定義されています．
ただし，微分可能でない点では値が 0 になります．
そのため，定理を使うときには `HasDerivAt` や `DifferentiableAt` の仮定が必要かを確認します．
-/

/-
---
## 微分の計算規則

和，積，合成などの微分公式は，`HasDerivAt` 版，`DifferentiableAt` 版，`deriv` 版など複数の形で用意されています．
まずは補題の型を `#check` で確認し，必要な仮定を揃えます．
-/

#check HasDerivAt.add
#check HasDerivAt.mul
#check HasDerivAt.comp
#check deriv_add
#check deriv_mul

section DerivativeRules

example {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x := by
  exact deriv_add hf hg

example {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  exact deriv_mul hf hg

example {f g : ℝ → ℝ} {x a b : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y + g y) (a + b) x := by
  exact hf.add hg

end DerivativeRules

/-
---
## Rolle の定理と平均値の定理

Mathlib には，実解析の基本定理も登録されています．
区間は `Set.Icc a b`，開区間は `Set.Ioo a b` として表します．
-/

#check exists_deriv_eq_zero
#check exists_deriv_eq_slope

section MeanValue

open Set

example {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  exact exists_deriv_eq_zero hab hfc hfI

example (f : ℝ → ℝ) {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  exact exists_deriv_eq_slope f hab hf hf'

end MeanValue

/-
---
## ノルム空間

一般の微分では，実数直線だけでなくノルム空間を扱います．
`NormedAddCommGroup E` はノルムを持つ加法可換群，
`NormedSpace ℝ E` は実ノルムベクトル空間です．
-/

#check NormedAddCommGroup
#check NormedSpace
#check norm_nonneg
#check norm_add_le

section NormedSpaces

variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ := by
  exact norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 := by
  exact norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  exact norm_add_le x y

example : PseudoMetricSpace E := by
  infer_instance

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ := by
  exact norm_smul a x

example [FiniteDimensional ℝ E] : CompleteSpace E := by
  infer_instance

end NormedSpaces

/-
有限次元ノルム空間が完備であることなど，解析の標準的な背景定理も型クラス探索で得られることがあります．
`infer_instance` は，必要な型クラスインスタンスを Lean に探させるコマンドです．
-/

/-
---
## 連続線形写像と Frechet 微分

ノルム空間の間の連続線形写像は `E →L[𝕜] F` です．
Frechet 微分では，導関数の値は連続線形写像になります．
-/

#check ContinuousLinearMap
#check HasFDerivAt
#check fderiv

section Frechet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f := by
  exact f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y := by
  exact f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x := by
  exact f.map_smul a x

example (f : E →L[𝕜] F) (x : E) : HasFDerivAt f f x := by
  exact f.hasFDerivAt

end Frechet

/-
`HasFDerivAt f f' x` は，「点 `x` での `f` の一次近似が連続線形写像 `f'` である」という意味です．
実数値関数の `HasDerivAt` は，この一般論の特殊な形として扱えます．
-/

/-
---
## 長めの例: 微分公式を組み合わせる

ここでは，関数

```text
f(x) = x^3 + 2x + 1
```

が `x = 5` で微分係数 `77` を持つことを示します．
紙の計算では `f'(x) = 3x^2 + 2` なので `f'(5) = 77` です．

Lean では，`HasDerivAt` の証明を組み合わせて同じことを表します．
-/

section PolynomialDerivativeExample

theorem cubicExample_hasDerivAt :
    HasDerivAt (fun x : ℝ => x ^ 3 + 2 * x + 1) (77 : ℝ) 5 := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 3) (3 * 5 ^ (3 - 1)) 5 := by
    simpa using (hasDerivAt_pow 3 (5 : ℝ))
  have hlin : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) 5 := by
    simpa using ((hasDerivAt_id (5 : ℝ)).const_mul (2 : ℝ))
  have h := (hpow.add hlin).add_const (1 : ℝ)
  convert h using 1
  norm_num

example : deriv (fun x : ℝ => x ^ 3 + 2 * x + 1) 5 = 77 := by
  exact cubicExample_hasDerivAt.deriv

end PolynomialDerivativeExample

/-
この例では，次の補題を使っています．

* `hasDerivAt_pow`: 冪関数の微分
* `hasDerivAt_id`: 恒等関数の微分
* `HasDerivAt.const_mul`: 定数倍の微分
* `HasDerivAt.add`: 和の微分
* `HasDerivAt.add_const`: 定数を足しても微分係数は変わらない

最後の `convert h using 1` は，Lean が持っている導関数の値
`3 * 5 ^ (3 - 1) + 2 * 1` と，目標の値 `77` を照合するために使っています．
残った数値計算は `norm_num` で閉じます．
-/

/-
---
## 長めの例: 閉区間上の Rolle の定理を使う

次の例は，Rolle の定理を直接使う演習です．
関数 `f` が閉区間 `[a, b]` で連続で，端点で同じ値を取るなら，
開区間 `(a, b)` のどこかで導関数が 0 になります．

この statement はこの章の前半にも出しましたが，ここでは「学部解析の定理をそのまま Lean の命題として読む」ことに注目します．
-/

section RolleExample

open Set

example {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hend : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  exact exists_deriv_eq_zero hab hcont hend

end RolleExample

/-
この定理を使うには，`ContinuousOn f (Icc a b)` が必要です．
微分可能性の仮定が statement に現れていないように見えますが，
Mathlib のこの定理は，一般の Rolle の定理のうち，導関数が定義上 0 になる点を含む形になっています．
より強い形や平均値の定理を使うときは，`DifferentiableOn ℝ f (Ioo a b)` が明示的に必要になります．
-/

/-
---
## まとめ

微分では，まず `HasDerivAt`，`DifferentiableAt`，`deriv` の違いを押さえることが重要です．
初等的な計算は `simp` や既存の微分公式で進みます．
より一般の解析では，ノルム空間，連続線形写像，Frechet 微分 `HasFDerivAt` が基本語彙になります．

### 形式化の tips

微分の形式化では，`deriv` の値を直接計算するより，まず `HasDerivAt` の証明を作る方が安定することがあります．

1. 点での微分係数を主張するなら `HasDerivAt`．
2. 微分可能性だけなら `DifferentiableAt`．
3. 導関数の値を式として使うなら `deriv`．
4. 多変数・ノルム空間なら `HasFDerivAt`．
5. 計算が詰まったら，`#check HasDerivAt.add` のように公式を探す．

---
## 演習問題

1. `fun x : ℝ => x ^ 4` が任意の点で微分可能であることを示してください．

    ```lean4
    example (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => y ^ 4) x := by
      -- `fun_prop` または `hasDerivAt_pow` から `.differentiableAt`．
      sorry
    ```

2. `x^2` の点 `3` における導関数が `6` であることを示してください．

    ```lean4
    example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
      -- `simp` と `norm_num` を試す．
      sorry
    ```

3. `HasDerivAt` の証明から `DifferentiableAt` を取り出してください．

    ```lean4
    example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) :
        DifferentiableAt ℝ f x := by
      -- ヒント: `exact h.differentiableAt`
      sorry
    ```

4. 積の微分公式を使って，`f * g` の導関数を表してください．

    ```lean4
    example {f g : ℝ → ℝ} {x : ℝ}
        (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
        deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
      -- ヒント: `exact deriv_mul hf hg`
      sorry
    ```

5. `E →L[ℝ] F` の元が連続関数として使えることを確認してください．

    ```lean4
    example {E F : Type*}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        (L : E →L[ℝ] F) :
        Continuous L := by
      -- ヒント: `exact L.cont`
      sorry
    ```

6. `HasFDerivAt` の statement を `#check` で表示し，実数 1 変数の `HasDerivAt` と何が違うか説明してください．

    ```lean4
    #check HasFDerivAt
    #check HasDerivAt
    ```

7. `x ↦ 3 * x ^ 2` の点 `2` における微分係数を `HasDerivAt` で示してください．

    ```lean4
    example : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (12 : ℝ) 2 := by
      -- `hasDerivAt_pow` と `.const_mul` を使う．
      sorry
    ```

8. 平均値の定理の statement を読み，`ContinuousOn` と `DifferentiableOn` の役割を説明してください．

    ```lean4
    #check exists_deriv_eq_slope
    ```

9. `ContinuousLinearMap.id` が任意の点で Frechet 微分として自分自身を持つことを確認してください．

    ```lean4
    example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
        HasFDerivAt (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) x := by
      -- ヒント: `exact (ContinuousLinearMap.id ℝ E).hasFDerivAt`
      sorry
    ```

10. `deriv` は微分不能な点で 0 と定義されることを，絶対値関数などで調べてください．

    ```lean4
    #check deriv_zero_of_not_differentiableAt
    ```
-/

--#--
example (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => y ^ 4) x := by
  -- `fun_prop` または `hasDerivAt_pow` から `.differentiableAt`．
  sorry

example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  -- `simp` と `norm_num` を試す．
  sorry

example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) :
    DifferentiableAt ℝ f x := by
  -- ヒント: `exact h.differentiableAt`
  sorry

example {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  -- ヒント: `exact deriv_mul hf hg`
  sorry

example {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) :
    Continuous L := by
  -- ヒント: `exact L.cont`
  sorry

#check HasFDerivAt
#check HasDerivAt

example : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (12 : ℝ) 2 := by
  -- `hasDerivAt_pow` と `.const_mul` を使う．
  sorry

#check exists_deriv_eq_slope

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    HasFDerivAt (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) x := by
  -- ヒント: `exact (ContinuousLinearMap.id ℝ E).hasFDerivAt`
  sorry

#check deriv_zero_of_not_differentiableAt
--#--

end --#

end PracticeChapter04 --#
