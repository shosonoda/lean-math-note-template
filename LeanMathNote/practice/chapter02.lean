--#--
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
--#--
/-
# Chapter 02: 線形代数

Mathlib における基本的な線形代数を扱います．

参考:
* Mathematics in Lean, 10. Linear Algebra: <https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html>
* Math in Lean: linear algebra: <https://leanprover-community.github.io/theories/linear_algebra.html>

主に次の対象が中心になります．

* `Module R M`: 加法群や加法モノイドの上のスカラー倍構造
* `V →ₗ[K] W`: 線形写像
* `Submodule K V`: 部分空間・部分加群
* `LinearIndependent`，`Basis`，`finrank`
* `Matrix m n R`: 行列

Mathlib では，ベクトル空間は専用の `VectorSpace` 型クラスではなく，体 `K` 上の `Module K V` として扱います．
これは半環上の半加群や環上の加群まで同じ枠組みで扱うためです．
-/
import Mathlib
set_option linter.missingDocs false --#

namespace PracticeChapter02

open scoped BigOperators
open scoped Matrix

/-
---
## `Module` とスカラー倍

「`K` を体，`V` を `K` ベクトル空間とする」は，Lean では次のように書きます．

```lean
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
```

`[AddCommGroup V]` と `[Module K V]` を分けて仮定するのは，型クラス探索を安定させるためです．
スカラー倍は `a • v` と書き，補題名では `smul` と呼ばれます．
-/

#check Module
#check SMul
#check smul_add
#check add_smul
#check smul_comm

section Modules

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

example (a : K) (u v : V) : a • (u + v) = a • u + a • v := by
  exact smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u := by
  exact add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u := by
  exact smul_comm a b u

example (u : V) : (0 : K) • u = 0 := by
  simp

end Modules

/-
`module` tactic は，加群の公理から従う等式を解くための tactic です．
`ring` や `group` と同じく，構造の公理に沿った正規化を行います．
-/

section ModuleTactic

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

example (a b : K) (x y : V) : a • (x + y) + b • x = (a + b) • x + a • y := by
  module

end ModuleTactic

/-
---
## 線形写像

`V →ₗ[K] W` は `K` 線形写像の型です．
これは関数と線形性の証明をまとめた bundled map です．
線形写像は関数として適用できますが，合成には `LinearMap.comp` または `∘ₗ` を使います．
-/

#check LinearMap
#check LinearEquiv

section LinearMaps

variable {K : Type*} [Field K]
variable {V W U : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup U] [Module K U]

example (φ : V →ₗ[K] W) (a : K) (v : V) : φ (a • v) = a • φ v := by
  exact map_smul φ a v

example (φ : V →ₗ[K] W) (v w : V) : φ (v + w) = φ v + φ w := by
  exact map_add φ v w

example (φ : V →ₗ[K] W) (ψ : W →ₗ[K] U) : V →ₗ[K] U :=
  ψ.comp φ

example (φ : V →ₗ[K] W) (ψ : W →ₗ[K] U) : V →ₗ[K] U :=
  ψ ∘ₗ φ

example : V →ₗ[K] V :=
  LinearMap.id

example (a : K) : V →ₗ[K] V :=
  LinearMap.lsmul K V a

#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

end LinearMaps

/-
線形写像どうしも加法やスカラー倍を持ちます．
そのため，線形写像の空間そのものをベクトル空間として扱えます．
-/

section LinearMapSpace

variable {K : Type*} [Field K]
variable {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

example (φ ψ : V →ₗ[K] W) (a : K) : V →ₗ[K] W :=
  a • φ + ψ

example (φ ψ : V →ₗ[K] W) (v : V) : (φ + ψ) v = φ v + ψ v := by
  rfl

end LinearMapSpace

/-
---
## 部分空間・部分加群

`Submodule K V` は，`V` の `K` 部分空間，より一般には部分加群です．
`Subgroup` や `Ideal` と同じく，台集合と閉性の証明を持つ bundled structure です．
-/

#check Submodule
#check Submodule.span

section Submodules

variable {K : Type*} [Field K]
variable {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

variable (S T : Submodule K V)

example {x y : V} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by
  exact S.add_mem hx hy

example {x : V} (a : K) (hx : x ∈ S) : a • x ∈ S := by
  exact S.smul_mem a hx

example : ((S ⊓ T : Submodule K V) : Set V) = (S : Set V) ∩ (T : Set V) := by
  rfl

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := by
  exact Submodule.mem_bot (R := K)

example (s : Set V) {x : V} (hx : x ∈ s) : x ∈ Submodule.span K s := by
  exact Submodule.subset_span hx

variable (φ : V →ₗ[K] W) (U : Submodule K W)

example : Submodule K W :=
  Submodule.map φ S

example : Submodule K V :=
  Submodule.comap φ U

example (x : V) : x ∈ Submodule.comap φ U ↔ φ x ∈ U := by
  rfl

#check LinearMap.ker
#check LinearMap.range

end Submodules

/-
`Submodule.span K s` は集合 `s : Set V` で張られる部分空間です．
部分空間の像と逆像は，線形写像に沿って `map` と `comap` で表されます．
これは実践編 Chapter 01 の部分群と同じ設計です．
-/

/-
---
## 一次独立・基底・次元

一次独立性は `LinearIndependent K v` で表します．
ここで `v : ι → V` は添字集合 `ι` で添字づけられたベクトルの族です．
基底は `Basis ι K V` で，添字集合 `ι` を持つ `K` 上の `V` の基底です．
-/

#check LinearIndependent
#check Module.Basis
#check Module.rank
#check Module.finrank

section Dimension

variable {K : Type*} [Field K]

example : Module.finrank K (Fin 3 → K) = 3 := by
  simp

example : Module.finrank K K = 1 := by
  simp

end Dimension

/-
`Module.rank` は基数値の次元です．
`FiniteDimensional.finrank` は自然数値の次元で，無限次元の場合は慣習的に 0 になります．
有限次元と分かっている状況では `finrank` が計算しやすいことが多いです．
-/

/-
---
## 行列

`Matrix m n R` は，行添字 `m`，列添字 `n`，成分型 `R` の行列です．
自然数ではなく任意の有限型で添字づけられる点が，紙の数学と少し違います．
`Fin m` を使うと，通常の `m` 行 `n` 列行列を表せます．
-/

#check Matrix
#check Matrix.of
#check Matrix.det
#check Matrix.toLin

section Matrices

variable {K : Type*} [Field K]

example (A B : Matrix (Fin 2) (Fin 3) K) (i : Fin 2) (j : Fin 3) :
    (A + B) i j = A i j + B i j := by
  rfl

example (A : Matrix (Fin 2) (Fin 3) K) (i : Fin 3) (j : Fin 2) :
    Aᵀ i j = A j i := by
  rfl

example (A : Matrix (Fin 2) (Fin 3) K) (v : Fin 3 → K) (i : Fin 2) :
    (A *ᵥ v) i = ∑ j, A i j * v j := by
  rfl

example : Matrix.det (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp

end Matrices

/-
行列は成分を計算したいときに便利です．
一方，抽象的な線形代数の証明では `LinearMap` を使う方が自然です．
基底を固定すると，線形写像と行列を対応させることができます．
-/

/-
---
## 長めの例: `K × K` 上の線形写像と kernel

ここでは，2 次元ベクトル空間 `K × K` から `K` への線形写像
`(x, y) ↦ x + y` を作ります．
紙の数学では当たり前に線形写像と呼ぶものも，Lean では `toFun`，`map_add'`，`map_smul'` を与えて構造体として作ります．
-/

section CoordinateLinearMaps

variable {K : Type*} [Field K]

def sumPairLinear : (K × K) →ₗ[K] K where
  toFun p := p.1 + p.2
  map_add' := by
    intro x y
    simp [add_left_comm, add_comm]
  map_smul' := by
    intro a x
    simp [mul_add]

example (x y : K) : sumPairLinear (x, y) = x + y := by
  rfl

example (x y : K) :
    (x, y) ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K) ↔ x + y = 0 := by
  rfl

/-
この kernel は，方程式 `x + y = 0` で定まる直線です．
Lean では，kernel は `Submodule K (K × K)` です．
つまり，単なる集合ではなく，線形部分空間としての閉性も持っています．
-/

#check LinearMap.ker

example (p q : K × K)
    (hp : p ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K))
    (hq : q ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K)) :
    p + q ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K) := by
  exact (LinearMap.ker sumPairLinear).add_mem hp hq

example (a : K) (p : K × K)
    (hp : p ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K)) :
    a • p ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K) := by
  exact (LinearMap.ker sumPairLinear).smul_mem a hp

/-
---
## 長めの例: 標準基底が `K × K` を張る

次に，`e₁ = (1, 0)` と `e₂ = (0, 1)` が `K × K` 全体を張ることを示します．
ここでは `Basis` を作るのではなく，まず `Submodule.span` だけを使います．

証明の中心は，任意の `p : K × K` について

```text
p = p.1 • e₁ + p.2 • e₂
```

を示すことです．
-/

def planeE1 : K × K :=
  (1, 0)

def planeE2 : K × K :=
  (0, 1)

example : Submodule.span K ({planeE1, planeE2} : Set (K × K)) = ⊤ := by
  ext p
  constructor
  · intro _
    trivial
  · intro _
    have hp : p = p.1 • planeE1 + p.2 • planeE2 := by
      ext <;> simp [planeE1, planeE2]
    rw [hp]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [planeE1]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [planeE2]))

end CoordinateLinearMaps

/-
この例では `ext p` で部分空間の等式を元ごとの同値に変換しています．
その後，`⊤` への所属は自明なので，全ての `p` が左辺の span に入ることを示せば十分です．

このような proof は，線形代数の形式化で頻繁に使う基本パターンです．

* span に生成元が入る: `Submodule.subset_span`
* span がスカラー倍で閉じる: `Submodule.smul_mem`
* span が和で閉じる: `Submodule.add_mem`
* 座標計算: `ext` と `simp`
-/

/-
---
## まとめ

Mathlib の線形代数では，ベクトル空間を `Module K V` として読みます．
線形写像 `V →ₗ[K] W`，部分空間 `Submodule K V`，行列 `Matrix m n R` は，いずれも数学的な構造とその公理を bundled structure として持ちます．

証明を書くときは，まず `#check` で補題の型を確認し，`simp`，`module`，`rw`，`ext`，`linear_combination` などを必要に応じて使います．

### 形式化の tips

線形代数の形式化では，紙の証明で省略している「どの空間の元か」を Lean に明示する必要があります．

1. 体 `K` とベクトル空間 `V` を分ける．
2. ベクトル空間は `[AddCommGroup V] [Module K V]` として仮定する．
3. 線形写像は関数ではなく `V →ₗ[K] W` として扱う．
4. 部分空間は `Submodule K V` であり，集合として使うときは coercion が働く．
5. span の証明では，生成元が span に入ることと，和・スカラー倍で閉じることを使う．
-/

/-
---
## 演習問題

以下の問題では，まず statement が何を意味しているかを自然言語で言い換えてから証明してください．
線形代数では，Lean の式と紙の数学の表現を往復する演習が重要です．

1. 線形写像は `0` を `0` に送ることを示してください．

    ```lean4
    example {K V W : Type*} [Field K]
        [AddCommGroup V] [Module K V]
        [AddCommGroup W] [Module K W]
        (f : V →ₗ[K] W) :
        f 0 = 0 := by
      -- `map_zero` または `simp`．
      sorry
    ```

2. kernel の元は，定義通り `f x = 0` を満たすことを示してください．

    ```lean4
    example {K V W : Type*} [Field K]
        [AddCommGroup V] [Module K V]
        [AddCommGroup W] [Module K W]
        (f : V →ₗ[K] W) (x : V) :
        x ∈ LinearMap.ker f ↔ f x = 0 := by
      -- `rfl` で閉じるか確認する．
      sorry
    ```

3. `Submodule.map` と `Submodule.comap` の membership を読み替えてください．

    ```lean4
    example {K V W : Type*} [Field K]
        [AddCommGroup V] [Module K V]
        [AddCommGroup W] [Module K W]
        (f : V →ₗ[K] W) (S : Submodule K V) (y : W) :
        y ∈ Submodule.map f S ↔ ∃ x ∈ S, f x = y := by
      -- `Submodule.mem_map` を調べる．
      sorry
    ```

4. `planeE1` と `planeE2` が一次独立であることを示してください．
これは少し難しい問題です．まず `#check LinearIndependent` で statement の形を確認してください．

    ```lean4
    example {K : Type*} [Field K] :
        LinearIndependent K (fun i : Fin 2 =>
          if i = 0 then (planeE1 : K × K) else planeE2) := by
      -- 方針: `linearIndependent_iff` 系の補題を探す．
      sorry
    ```

5. `K × K` 上の線形写像 `(x, y) ↦ x - y` を `LinearMap` として作ってください．

    ```lean4
    def diffPairLinear {K : Type*} [Field K] : (K × K) →ₗ[K] K where
      toFun p := p.1 - p.2
      map_add' := by
        -- 座標計算．
        sorry
      map_smul' := by
        -- スカラー倍の分配法則．
        sorry
    ```

6. `Matrix (Fin 2) (Fin 2) K` の単位行列の行列式が 1 であることを，`simp` 以外の方法でも調べてください．

    ```lean4
    #check Matrix.det_one
    ```

7. `sumPairLinear` の kernel が `x + y = 0` であることを，`rfl` ではなく `simp` で証明してください．

    ```lean4
    example {K : Type*} [Field K] (x y : K) :
        (x, y) ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K) ↔ x + y = 0 := by
      -- `show` でゴールを見てから `simp [sumPairLinear]` を試す．
      sorry
    ```

8. 線形写像の range が部分空間であることを確認してください．

    ```lean4
    example {K V W : Type*} [Field K]
        [AddCommGroup V] [Module K V]
        [AddCommGroup W] [Module K W]
        (f : V →ₗ[K] W) :
        Submodule K W :=
      LinearMap.range f
    ```

9. `K × K` の任意の点を `planeE1` と `planeE2` の線形結合として書いてください．

    ```lean4
    example {K : Type*} [Field K] (p : K × K) :
        p = p.1 • planeE1 + p.2 • planeE2 := by
      -- ヒント: `ext <;> simp [planeE1, planeE2]`
      sorry
    ```

10. 行列と線形写像の橋渡しとして `Matrix.toLin` の型を読み，どこで基底が必要になるか説明してください．

    ```lean4
    #check Matrix.toLin
    ```
-/

--#--
example {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) :
    f 0 = 0 := by
  -- `map_zero` または `simp`．
  sorry

example {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (x : V) :
    x ∈ LinearMap.ker f ↔ f x = 0 := by
  -- `rfl` で閉じるか確認する．
  sorry

example {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (S : Submodule K V) (y : W) :
    y ∈ Submodule.map f S ↔ ∃ x ∈ S, f x = y := by
  -- `Submodule.mem_map` を調べる．
  sorry

example {K : Type*} [Field K] :
    LinearIndependent K (fun i : Fin 2 =>
      if i = 0 then (planeE1 : K × K) else planeE2) := by
  -- 方針: `linearIndependent_iff` 系の補題を探す．
  sorry

def diffPairLinear {K : Type*} [Field K] : (K × K) →ₗ[K] K where
  toFun p := p.1 - p.2
  map_add' := by
    -- 座標計算．
    sorry
  map_smul' := by
    -- スカラー倍の分配法則．
    sorry

#check Matrix.det_one

example {K : Type*} [Field K] (x y : K) :
    (x, y) ∈ LinearMap.ker (sumPairLinear : (K × K) →ₗ[K] K) ↔ x + y = 0 := by
  -- `show` でゴールを見てから `simp [sumPairLinear]` を試す．
  sorry

example {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) :
    Submodule K W :=
  LinearMap.range f

example {K : Type*} [Field K] (p : K × K) :
    p = p.1 • planeE1 + p.2 • planeE2 := by
  -- ヒント: `ext <;> simp [planeE1, planeE2]`
  sorry

#check Matrix.toLin
--#--

end PracticeChapter02 --#
