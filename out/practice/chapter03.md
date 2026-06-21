# Chapter 03: 位相

Mathlib における基本的な位相を扱います．

参考:

* Mathematics in Lean, 11. Topology: <https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html>
* Maths in Lean: Topological, uniform and metric spaces: <https://leanprover-community.github.io/theories/topology.html>

フィルター，距離空間，位相空間，連続性，コンパクト性などが説明されています．

Lean での位相はフィルターに基づいて形式化されています．
フィルターは，数列の極限，関数の極限，無限遠での振る舞い，近傍，ほとんど至る所，などを同じ言葉で扱うための道具です．

```lean
import Mathlib

namespace PracticeChapter03

open Set Filter
open scoped Topology
```

---
## 位相空間

位相空間構造は `TopologicalSpace X` です．
開集合は `IsOpen U`，閉集合は `IsClosed C` と書きます．
`interior`，`closure`，`frontier` なども `Set X` に対する操作です．

```lean
#check TopologicalSpace
#check IsOpen
#check IsClosed
#check interior
#check closure
#check frontier

section TopologicalSpaces

variable {X : Type*} [TopologicalSpace X]
variable {U V C D Y Z : Set X}

example (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) := by
  exact hU.inter hV

example (hC : IsClosed C) (hD : IsClosed D) : IsClosed (C ∪ D) := by
  exact hC.union hD

example : IsOpen Cᶜ ↔ IsClosed C := by
  exact isOpen_compl_iff

example : interior Y = Y ↔ IsOpen Y := by
  exact interior_eq_iff_isOpen

example (hYZ : Y ⊆ Z) : interior Y ⊆ interior Z := by
  exact interior_mono hYZ

example : closure Y = Y ↔ IsClosed Y := by
  exact closure_eq_iff_isClosed

example (hYZ : Y ⊆ Z) : closure Y ⊆ closure Z := by
  exact closure_mono hYZ

end TopologicalSpaces
```

集合の等式や包含と同じように，位相的な操作も `Set` の補題と組み合わせて使います．
たとえば，`closure_mono` は集合の包含から閉包の包含を得る補題です．

---
## 距離空間

距離空間や擬距離空間では，`dist x y`，開球 `Metric.ball x ε`，閉球 `Metric.closedBall x ε` などを使います．
距離空間は位相空間構造を誘導するため，距離の話から `IsOpen` や `Continuous` の話へ移れます．

```lean
#check PseudoMetricSpace
#check Metric.ball
#check Metric.closedBall
#check dist

section MetricSpaces

open Metric

variable {X : Type*} [PseudoMetricSpace X]

example (x : X) : dist x x = 0 := by
  simp

example (x y : X) : 0 ≤ dist x y := by
  exact dist_nonneg

example (x : X) (ε : ℝ) (hε : 0 < ε) : x ∈ Metric.ball x ε := by
  simpa [Metric.mem_ball] using hε

example (x : X) (ε : ℝ) : IsOpen (Metric.ball x ε) := by
  exact Metric.isOpen_ball

end MetricSpaces
```

`Metric.ball x ε` は集合です．
したがって `x ∈ Metric.ball x ε` や `IsOpen (Metric.ball x ε)` のように，集合に関する命題として扱えます．

---
## コンパクト性

コンパクト性は `IsCompact s` で表されます．
これは `s : Set X` に対する述語です．
閉集合や連続写像との相互作用は，解析や微分積分で頻繁に使います．

```lean
#check IsCompact
#check IsCompact.image
#check IsClosed

section Compactness

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {f : X → Y}

example (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) := by
  exact hs.image hf

end Compactness
```

---
## フィルター

`Filter α` は，`α` の部分集合の集まりに閉性条件を入れた構造です．
距離空間での点列の収束を一般化するために使われます．
数学的には，集合 $\alpha$ 上のフィルター $F \subset \mathcal P(\alpha)$ は，$\alpha$ の部分集合からなる族で，次を満たすものです．

* 全体集合 $\alpha$ を含む: $\alpha \in F$
* 空集合 $\emptyset$ を含まない: $\emptyset \notin F$
* 上に閉じている: $U \in F, V \in \mathcal P(\alpha)$ かつ $U \subset V$ なら $V \in F$．
* 共通部分演算で閉じている: $U,V \in F$ なら $U \cap V \in F$．

ただし Lean の `Filter α` は技術的な都合で `∅` を含む退化したフィルターも許します．退化していないこと（真のフィルター）が必要な場面では，`NeBot l` という型クラスを仮定します．

記法 `∀ᶠ x in l, p x` は，「フィルター `l` の意味で十分近い，あるいは十分先の `x` について `p x` が成り立つ」という意味です．
定義上は，集合 `{x | p x}` がフィルター `l` に属する，という主張です．

代表例は次の通りです．

* `atTop`: 十分大きい値に対応するフィルター
* `𝓝 x`: 点 `x` の近傍フィルター（点 $x$ の近傍全体 $\mathcal N(x)$）．`s ∈ 𝓝 x` は，`x` を含む開集合が `s` に含まれることを意味する．
* `ae μ`: 測度 `μ` に関してほとんど至る所成り立つ，というフィルター

```lean
#check Filter
#check Tendsto
#check atTop
#check 𝓝
#check Filter.Eventually

section Filters

example {α : Type*} {l : Filter α} {p : α → Prop} :
    (∀ᶠ x in l, p x) = ({x | p x} ∈ l) := by
  rfl

example : (∀ᶠ n in (atTop : Filter Nat), 3 ≤ n) := by
  exact eventually_ge_atTop 3

example {X : Type*} [TopologicalSpace X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  exact mem_nhds_iff

example {α β : Type*} {f : α → β} {l : Filter α} {m : Filter β} :
    Tendsto f l m = (map f l ≤ m) := by
  rfl

end Filters
```

`Tendsto f l m` は，「`x` がフィルター `l` に沿って動くとき，`f x` がフィルター `m` に沿って動く」という意味です．
数列の極限も，関数の一点での極限も，無限遠での極限も，この形で表されます．

---
## 具体的な極限計算

実数列 $a_n$ が $+\infty$ に発散することは，Lean では

```lean4
Tendsto a atTop atTop
```

と書きます．

たとえば，自然数を実数に埋め込んだ列 $n \mapsto n$ は `atTop` に収束します．

```lean
section ConcreteLimits

example : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop
```

一点での関数の極限は，始域側を `𝓝 a`，終域側を `𝓝 b` として

```lean4
Tendsto f (𝓝 a) (𝓝 b)
```

と書きます．

以下は $\lim_{x \to 2} (x+3) = 5$ です．
`Continuous.tendsto` は，連続性からその点での極限を取り出す補題です．
最後の `norm_num` は，`2 + 3 = 5` の数値計算を処理しています．

```lean
example : Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 5) := by
  convert (((continuous_id : Continuous fun x : ℝ => x).add
    (continuous_const : Continuous fun _ : ℝ => (3 : ℝ))).tendsto (2 : ℝ)) using 1
  norm_num
```

ここで使っている `convert` は，手元にある定理の結論が現在のゴールと「ほとんど同じ」だが，
一部の式だけがまだ一致していないときに便利な tactic です．

上の例では，連続性から得られる極限はまず

```lean4
Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 (2 + 3))
```

という形です．
一方，示したいゴールは終域側が `𝓝 5` です．
`convert ... using 1` は，この 2 つの主張を対応させたうえで，
残った差分 `2 + 3 = 5` を新しいゴールとして残します．
最後の `norm_num` がその数値計算を閉じています．

同じ方針で，多項式や初等関数の極限も計算できます．
次は $\lim_{x \to 3} (x^2+1) = 10$ と
$\lim_{x \to 0}(\sin x + x^2)=0$ です．

```lean
example : Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 10) := by
  convert ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ)) using 1
  norm_num

example : Tendsto (fun x : ℝ => Real.sin x + x ^ 2) (𝓝 0) (𝓝 0) := by
  simpa using ((by continuity : Continuous fun x : ℝ => Real.sin x + x ^ 2).tendsto (0 : ℝ))
```

無限遠での極限も同じ `Tendsto` です．
次は $\lim_{x \to +\infty} 1/x = 0$ です．
ここでは始域側のフィルターが `atTop`，終域側のフィルターが `𝓝 0` になっています．

```lean
example : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

end ConcreteLimits
```

---
## 連続性

関数 `f : X → Y` の連続性は `Continuous f` です．
一点 `x` での連続性は `ContinuousAt f x`，集合 `s` 上の連続性は `ContinuousOn f s` です．
Mathlib では，一点での連続性がフィルターで定義されています:

```lean title="Mathlib.Topology.Defs"
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
```

これは「`x` に十分近い点を `f` で送ると，`f x` に十分近い点になる」という意味です．
より展開すると，`f x` の任意の近傍 `A` に対して，その逆像 `f ⁻¹' A` が `x` の近傍である，という条件になります．
位相空間の教科書では大域的な連続性を「開集合の逆像が開集合」と定義することが多いですが，
フィルターを使うと点での連続性，数列や関数の極限，無限遠での極限を同じ `Tendsto` の形で扱えます．

距離空間では，この定義は通常の `ε`-`δ` に戻ります．
`ContinuousAt f a` は「任意の `ε > 0` に対して，ある `δ > 0` が存在して，`dist x a < δ` なら `dist (f x) (f a) < ε`」という条件と同値です．

```lean
#check Continuous
#check ContinuousAt
#check ContinuousOn

section Continuity

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example {f : X → Y} {x : X} :
    ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
  rfl

example {f : X → Y} {x : X} :
    ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x := by
  exact continuousAt_def

example {α : Type*} {f : α → Y} {l : Filter α} {y : Y} :
    Tendsto f l (𝓝 y) ↔ ∀ s : Set Y, IsOpen s → y ∈ s → f ⁻¹' s ∈ l := by
  exact tendsto_nhds

example {f : X → Y} (hf : Continuous f) (x : X) : ContinuousAt f x := by
  exact hf.continuousAt

example {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => g (f x) := by
  exact hg.comp hf

example : Continuous fun x : ℝ => x ^ 2 + 1 := by
  continuity

example : ContinuousAt (fun x : ℝ => Real.sin x + x ^ 2) (0 : ℝ) := by
  simpa using
    (Real.continuous_sin.continuousAt.add
      ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2))

example {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
      dist x a < δ → dist (f x) (f a) < ε := by
  exact Metric.continuousAt_iff
```

具体的な関数の連続性は，初等関数・四則演算・合成に関する補題を組み合わせて示します．
`continuity` tactic はこの組み合わせを自動で行います．
たとえば，$x \mapsto \sin x + x^2$ は実数上連続です．

```lean
example : Continuous fun x : ℝ => Real.sin x + x ^ 2 := by
  continuity
```

分母を持つ関数では，分母が 0 でないことが必要です．
一点での連続性なら，その点で分母が 0 でないことを示せば十分です．
次は $x=0$ における

```text
(x^2+1)/(x+3)
```

の連続性です．

```lean
example : ContinuousAt (fun x : ℝ => (x ^ 2 + 1) / (x + 3)) 0 := by
  exact (((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2).add
    continuousAt_const).div
    ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).add continuousAt_const)
    (by norm_num)
```

大域的な連続性では，すべての点で分母が 0 でないことを示します．
次の例では $x^2+2>0$ なので分母は 0 になりません．

```lean
example : Continuous fun x : ℝ => (x ^ 2 + 1) / (x ^ 2 + 2) := by
  exact (((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const).div
    (((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const)
    (by
      intro x
      positivity)
```

`Metric.continuousAt_iff` を使うと，具体的な関数の連続性から
`ε`-`δ` 条件を取り出せます．
次は $x \mapsto x+1$ が $x=3$ で連続であることを，
距離による条件として読み替えた例です．

```lean
example : ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
    dist x 3 < δ → dist (x + 1) ((3 : ℝ) + 1) < ε := by
  have h : ContinuousAt (fun y : ℝ => y + 1) (3 : ℝ) := by
    exact (continuousAt_id : ContinuousAt (fun y : ℝ => y) 3).add continuousAt_const
  exact Metric.continuousAt_iff.mp h

end Continuity
```

実数上の初等関数の連続性は `continuity` tactic で証明できることが多いです．
失敗した場合は，`Continuous.add`，`Continuous.mul`，`Continuous.comp` などの補題を明示的に使います．

---
## 長めの例: 連続関数の零点集合は閉集合

位相の典型的な主張として，連続関数 `f : X → ℝ` の零点集合

```text
{x | f x = 0}
```

は閉集合です．
紙の証明では「`{0}` は `ℝ` の閉集合で，零点集合はその逆像である」と説明します．
Lean でも同じ構造で証明します．

```lean
def zeroSet {X : Type*} (f : X → ℝ) : Set X :=
  {x | f x = 0}

section ZeroSet

variable {X : Type*} [TopologicalSpace X]
variable {f : X → ℝ}

example (hf : Continuous f) : IsClosed (zeroSet f) := by
  simpa [zeroSet] using isClosed_singleton.preimage hf

example (hf : Continuous f) (c : ℝ) : IsClosed {x : X | f x = c} := by
  simpa using isClosed_eq hf continuous_const

end ZeroSet
```

2 つ目の例は，level set `{x | f x = c}` が閉集合であることを示しています．
証明では `{x | f x = c}` を `{x | f x - c = 0}` と見て，
連続関数 `x ↦ f x - c` の零点集合として扱っています．

`simpa` は，このような表現の差を整理するためによく使います．

---
## 長めの例: compact set の連続像

コンパクト集合の連続像はコンパクトです．
さらに，値域が Hausdorff 空間ならコンパクト集合は閉集合です．
したがって，Hausdorff 空間への連続写像では，コンパクト集合の像は閉集合になります．

```lean
section CompactImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
variable {s : Set X} {f : X → Y}

example (hs : IsCompact s) (hf : Continuous f) : IsClosed (f '' s) := by
  exact (hs.image hf).isClosed

end CompactImage
```

ここで `[T2Space Y]` は，`Y` が Hausdorff 空間であるという型クラス仮定です．
定理 `IsCompact.isClosed` は一般の位相空間では成り立たず，Hausdorff 条件を要求します．
型クラス仮定として必要な位相的条件が明示されるのは，Mathlib の位相の読み方で重要です．

---
## まとめ

Mathlib の位相では，極限を直接 `ε`-`δ` で定義するのではなく，フィルター `Tendsto` を基礎にします．
開集合・閉集合・閉包・内部は `Set` 上の述語や操作として扱われます．
距離空間では `Metric.ball` や `dist` を使い，連続性は `Continuous`，`ContinuousAt`，`ContinuousOn` で表します．
特に `ContinuousAt f x` は `Tendsto f (𝓝 x) (𝓝 (f x))` なので，点での連続性もフィルターの極限として読めます．

微分と積分の章では，これらの位相的な語彙がそのまま使われます．

### 形式化の tips

位相の形式化では，同じ定理が「集合の言葉」「フィルターの言葉」「距離の言葉」で出てきます．
どのレベルで証明するかを選ぶのが重要です．

1. 開集合・閉集合の問題なら `IsOpen`，`IsClosed` を探す．
2. 極限の問題なら `Tendsto` と `𝓝` を読む．
3. 距離空間の問題なら `Metric.ball`，`dist`，`Metric.mem_ball` を使う．
4. 連続性の合成なら `Continuous.comp` または `hg.comp hf` を使う．
5. compactness では，Hausdorff 条件 `[T2Space X]` が必要かを確認する．

---
## 演習問題

1. 開集合の連続写像による逆像が開集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
        IsOpen (f ⁻¹' U) := by
      -- `hU.preimage hf` を試す．
      sorry
    ```

2. 閉集合の連続写像による逆像が閉集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {C : Set Y} (hC : IsClosed C) :
        IsClosed (f ⁻¹' C) := by
      -- `hC.preimage hf` を試す．
      sorry
    ```

3. 実数値連続関数 `f g : X → ℝ` について，集合 `{x | f x ≤ g x}` が閉集合であることを示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsClosed {x : X | f x ≤ g x} := by
      -- `isClosed_le hf hg` を調べる．
      sorry
    ```

4. 距離空間で，開球が開集合であることをもう一度証明してください．

    ```lean4
    example {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
        IsOpen (Metric.ball x r) := by
      -- `Metric.isOpen_ball`．
      sorry
    ```

5. `Tendsto` の定義を `map` と filter の順序として読み替えてください．

    ```lean4
    example {α β : Type*} (f : α → β) (l : Filter α) (m : Filter β) :
        Tendsto f l m = (map f l ≤ m) := by
      -- 定義そのもの．
      sorry
    ```

6. `closure_mono` を使って，`s ⊆ t` なら `closure s ⊆ closure t` を示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
        closure s ⊆ closure t := by
      -- ヒント: `exact closure_mono hst`
      sorry
    ```

7. `zeroSet` を使わずに `{x | f x = 0}` が閉集合であることを直接証明してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
        IsClosed {x : X | f x = 0} := by
      -- `isClosed_eq hf continuous_const` を使う．
      sorry
    ```

8. `{x | f x < g x}` が開集合であることを調べてください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsOpen {x : X | f x < g x} := by
      -- `isOpen_lt hf hg` を調べる．
      sorry
    ```

9. `ContinuousAt` が `Tendsto` であることを確認してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} {x : X} :
        ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
      -- ヒント: `rfl`
      sorry
    ```

10. 距離空間で，`ContinuousAt` が `ε`-`δ` 条件と同値であることを確認してください．

    ```lean4
    example {f : ℝ → ℝ} {a : ℝ} :
        ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
          dist x a < δ → dist (f x) (f a) < ε := by
      -- ヒント: `exact Metric.continuousAt_iff`
      sorry
    ```

11. `interior s ⊆ s` と `s ⊆ closure s` をそれぞれ確認してください．

    ```lean4
    #check interior_subset
    #check subset_closure
    ```
