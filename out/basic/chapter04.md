# Chapter 04: Mathlib を用いた証明の書き方

この章では，Mathlib を使って証明を書くときの基本的な読み方・書き方を整理します．
線形代数や微積分の各論は実践編で扱い，ここではそれらに共通する Mathlib の基本的な使い方を見ます．

Mathlib は，Lean の上で通常の数学を形式化するための大規模なライブラリです．
群・環・体・位相空間・測度・多様体などの定義，それらに関する定理，記法，型クラスインスタンス，証明を補助する tactic が含まれています．
Lean 本体の小さなカーネルが証明の正しさを検査し，Mathlib はその上に数学の語彙と既存定理を積み上げている，と考えるとよいです．
したがって，Mathlib を import しても「証明を信用で通す」わけではなく，最終的な証明項は Lean のカーネルで型検査されます．

特に次の内容を扱います．

* `import Mathlib` と名前空間・スコープつき記法
* 型クラスと階層
* `Set`，`Finset`，`Real`，`NNReal`，`EReal`，`ENNReal`
* bundled structure，morphism，subobject，coercion
* 不等式の型と証明パターン
* Mathlib でよく使う tactic と検索支援
* Mathlib の命名規則

なお，`Set α`，`Finset α`，`Real`，`NNReal`，`EReal`，`ENNReal` は「クラス」ではなく型です．
ただし，それらの型には `LinearOrder`，`TopologicalSpace`，`CompleteLinearOrder` などの型クラスインスタンスが登録されており，そのインスタンスによって一般定理や tactic が使えるようになります．
Mathlib を読むときは，「対象そのものの型」と「その型に入っている構造」を分けて見ることが重要です．

参考:

* Mathematics in Lean: <https://leanprover-community.github.io/mathematics_in_lean/index.html>
* Mathlib overview: <https://leanprover-community.github.io/mathlib-overview.html>
* Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>

```lean
import Mathlib

namespace Chapter04
```

---
## `import Mathlib` と `open scoped`

このプロジェクトでは各章の冒頭で `import Mathlib` を使っています．これは Mathlib 全体を読み込みます．
実際の開発では，ビルド時間を抑えるために必要なファイルだけを import することもあります．
たとえば `import Mathlib.Data.Real.Basic` や `import Mathlib.Topology.Basic` のように，必要な分野のファイルだけを import する書き方です．
`import Mathlib` は「Mathlib に含まれる主要な定義・定理・tactic をまとめて使えるようにする」指定であり，Lean の言語機能そのものとは区別します．

一部の記法は，スコープを開かないと使えません．
有限和 `∑` には `BigOperators`，拡張非負実数の `∞` には `ENNReal` のスコープを使います．
`open scoped` は名前空間の中の定義名を短くするというより，特定の記法やスコープ付き記法を有効にするために使います．

Mathlib では，定義そのものと記法が分かれていることがよくあります．
たとえば `Real` という型には `ℝ` という記法があり，`NNReal` には `ℝ≥0`，`ENNReal` には `ℝ≥0∞` という記法があります．
また `∑ i ∈ s, f i` は有限和を表す記法で，背後には `Finset.sum` があります．
証明中で記法の意味が分からなくなったら，`#check` で型を確認し，必要なら対応する定義名を探します．

```lean
open scoped BigOperators
open scoped ENNReal
open scoped NNReal
```

`#check` は，Mathlib の名前がどのような型をもつかを確認する基本コマンドです．
`#synth` は，指定した型クラスインスタンスを Lean が見つけられるかを確認します．

```lean
#check Finset
#check Set
#check Real
#check NNReal
#check EReal
#check ENNReal
#check ℝ
#check ℝ≥0
#check ℝ≥0∞
#check (∞ : ℝ≥0∞)

#synth Field ℝ
#synth LinearOrder ℝ
#synth TopologicalSpace ℝ
#synth Add ENNReal
#synth CompleteLinearOrder ENNReal
```

---
## 型クラスで一般化された定理を読む

Mathlib の定理は，特定の型だけではなく，型クラスで一般化された形で書かれることがよくあります．
たとえば `add_comm` は自然数専用の定理ではなく，足し算が可換な任意の型で使える定理です．
`#check add_comm` の結果を見ると，必要な型クラス仮定が明示されます．

```lean
#check add_comm
#check add_zero
#check le_total

section GenericAlgebra

variable {α : Type*} [AddCommMonoid α]

example (a b : α) : a + b = b + a := by
  exact add_comm a b

example (a : α) : a + 0 = a := by
  exact add_zero a

end GenericAlgebra
```

角括弧 `[AddCommMonoid α]` は，「`α` には加法可換モノイド構造がある」というインスタンスを要求します．
Lean はこの仮定を使って `+` や `0` の意味を決め，`add_comm` や `add_zero` を適用します．
実際には `add_comm` だけならより弱い `AddCommMagma` で十分ですが，ここでは `add_zero` も同じ section で使うため `AddCommMonoid` を仮定しています．
`Type*` は universe レベルを Lean に推論させる記法で，`Type u` の universe 変数を明示しない書き方です．

```lean
section GenericOrder

variable {α : Type*} [LinearOrder α]

example (a b : α) : a ≤ b ∨ b ≤ a := by
  exact le_total a b

end GenericOrder
```

このように，Mathlib の多くの定理は「型 `α` と，その型に入っている構造」を分けて書きます．
後半の章で現れる `Group`，`Ring`，`TopologicalSpace`，`Module` なども同じ発想です．

```lean
#check Group
#check Ring
#check TopologicalSpace
#check Module
```

---
## `Set`: 型の上の集合

Lean は型理論を基礎にしているため，「集合」は型として定義されます．
たとえば自然数全体は `Nat`，実数全体は `ℝ` という型です．
`Set α` は「型 `α` の部分集合」の型を表します．
定義は単純で，`Set α` は `α → Prop` として実装されています．

```lean title="Mathlib.Data.Set.Defs"
def Set (α : Type u) := α → Prop
```

つまり，`s : Set α` とは，各 `x : α` に対して「`x` が `s` に属する」という命題を返す述語です．
所属 `x ∈ s` は，内部的には `s x` と同じ意味です．
この意味で，Lean の `Set α` は固定された型 `α` 上の部分集合全体，つまり冪集合 $\mathcal P(\alpha)$ に対応します．
ただし実際の証明では，`Set` が関数として実装されていることを直接展開するより，`{x | p x}` や `x ∈ s` や `s ⊆ t` のような集合のインターフェースを使うのが普通です．

対応を大まかに書くと，次のようになります．

* 全体集合・台集合 $\alpha$: Lean では多くの場合 `α : Type*`
* 部分集合 $s \subseteq \alpha$: Lean では `s : Set α`
* 冪集合 $\mathcal P(\alpha)$: Lean では `Set α` という型
* 条件 $x \in s$: Lean では命題 `x ∈ s`

```lean
#check Set
#check Set.powerset
#check Set.ext
#check Set.mem_setOf
#check Set.setOf_bijective

def smallSet : Set Nat :=
  {n | n < 3}

example (n : Nat) : n ∈ smallSet ↔ n < 3 := by
  rfl

example : 2 ∈ smallSet := by
  norm_num [smallSet]

example : 4 ∉ smallSet := by
  norm_num [smallSet]

example (s t : Set Nat) : t ∈ Set.powerset s ↔ t ⊆ s := by
  exact Set.mem_powerset_iff t s
```

集合の等式は，通常，外延性で証明します．
数学で「任意の `x` について `x ∈ A` と `x ∈ B` が同値だから `A = B`」と言う議論に対応するのが `Set.ext` や tactic の `ext` です．

```lean
example (A B : Set Nat) : A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]
```

`Set α` と似て見えるものに `Subtype` があります．
`s : Set α` は `α` 上の述語であり，それ自体は `Set α` 型の項です．
一方，`{x : α // x ∈ s}` は，`s` に属する元だけを集めた新しい型です．
要素は値 `x : α` と証明 `x ∈ s` の組です．

Mathlib では `s : Set α` を型として使うと，この subtype へ coercion されます．
たとえば `x : smallSubtype` は「`smallSet` の元」としてのデータであり，`(x : Nat)` に戻すと元の自然数が得られます．

```lean
abbrev smallSubtype : Type :=
  {n : Nat // n ∈ smallSet}

#check Subtype
#check Set.coe_eq_subtype
#check Subtype.mem

example : (⟨2, by norm_num [smallSet]⟩ : smallSubtype).1 = 2 := by
  rfl

example (x : smallSubtype) : (x : Nat) ∈ smallSet := by
  exact x.property
```

---
## `Finset`: 有限集合

`Finset α` は，型 `α` の元からなる有限集合です．
リストとは違い，重複を持たない集合として扱います．
一方で，有限集合なので `card`，有限和 `∑`，有限積 `∏` などを使えます．
`Finset α` は `Set α` に有限性を付けたものというより，有限個の要素をデータとして持つ型です．
そのため，計算や有限和・有限積との相性がよい一方，一般の集合論的な部分集合は `Set α` で表します．

Mathlib では，有限な対象や集合的な対象を表す方法がいくつかあります．

* `List α`: 順序と重複を持つ有限列です．計算や再帰に向いています．
* `Multiset α`: 順序を無視し，重複は残す有限多重集合です．
* `Set α`: `α → Prop` として実装される，型 `α` の部分集合です．有限とは限りません．
* `Finset α`: 順序も重複も無視する有限集合です．有限和や有限積の添字に向いています．
* `Fintype α`: 型 `α` のすべての元が有限個である，という型クラスです．
* `Subtype`: 条件を満たす元を新しい型として扱う方法です．

したがって，順序つきのデータとして扱いたいなら `List`，重複個数を気にするなら `Multiset`，有限集合として和や濃度を扱いたいなら `Finset`，型 `α` の一般の部分集合なら `Set α` を使います．

多くの操作では，元の等号を判定できること，つまり `[DecidableEq α]` が必要になります．
自然数 `Nat` にはそのインスタンスがあるため，次の例はそのまま動きます．
たとえば，要素を挿入したときに既に含まれているかどうかを判定するには，要素同士の等号を決定できる必要があります．

```lean
#check List
#check Multiset
#check Finset
#check Fintype

example : (([1, 2, 1] : List Nat) : Multiset Nat) = (([1, 1, 2] : List Nat) : Multiset Nat) := by
  decide

example : ({1, 1, 2} : Finset Nat).card = 2 := by
  native_decide

example : ({1, 2} : Finset Nat) = ({2, 1} : Finset Nat) := by
  native_decide

example : (3 : Nat) ∈ Finset.range 5 := by
  simp

example : (5 : Nat) ∉ Finset.range 5 := by
  simp

example : (Finset.range 5).card = 5 := by
  simp
```

`Finset.range n` は `{0, 1, ..., n - 1}` です．
有限和は `∑ i ∈ s, f i` の形で書けます．

```lean
example : (∑ i ∈ Finset.range 4, i) = 6 := by
  native_decide
```

`native_decide` は，決定可能な命題を実行時に計算して証明します．
有限集合の小さな具体例では便利ですが，一般の数学的証明では `simp`，`rw`，補題を使って構造的に示すのが普通です．

`Fintype α` は「型 `α` 全体が有限である」という型クラスです．
たとえば `Fin 3` は 3 個の元を持つ型で，`Finset.univ` はその型の全要素からなる有限集合です．
`Finset α` は「有限個の `α` の要素を集めたデータ」であり，`Fintype α` は「型 `α` 自身が有限である」という構造です．

```lean
example : Fintype.card (Fin 3) = 3 := by
  rfl

example : (Finset.univ : Finset (Fin 3)).card = 3 := by
  rfl
```

`Finset` と `Set` は相互に関係しますが，同じものではありません．
`Finset` は有限性をデータとして持つため，和や積を直接定義できます．
`Set α` は単に `α → Prop` なので，有限とは限らず，有限和には追加の有限性情報が必要です．

---
## `Real`, `NNReal`, `EReal`, `ENNReal`: 実数系の型

数学では実数の構成として，Dedekind cut，Cauchy 列による完備化，完備順序体としての公理化など，いくつかの標準的な方法があります．
Mathlib の `Real` は，実装上は有理数の Cauchy 列の同値類として構成されています．
ただし，通常の形式化ではこの構成を直接展開することはほとんどありません．
実用上は，`ℝ` が体，線形順序，位相空間，完備距離空間，条件付き完備線形順序などの構造を持つ型である，というインターフェースを使います．

プログラミング言語の `Float` とも違います．
Lean の `ℝ` は有限精度の浮動小数点数ではなく，証明対象としての数学的な実数です．
丸め誤差を含む計算ではなく，定理として `a + b = b + a` や中間値の定理，完備性などを扱うための型です．

Mathlib.Data 配下には，実数そのものに加えて，非負実数や拡張実数を表す型が用意されています．

| 型 | 記法 | 構成 | 主な用途 |
|---|---|---|---|
| `Real` | `ℝ` | 有理数 Cauchy 列の同値類 | 通常の実解析，代数，位相 |
| `NNReal` | `ℝ≥0` | `{r : ℝ // 0 ≤ r}` | 非負量，距離，ノルム，確率など |
| `ENNReal` | `ℝ≥0∞` | `WithTop ℝ≥0` | 測度，拡張距離，`∞` を許す非負量 |
| `EReal` | なし | `WithBot (WithTop ℝ)` | `[-∞, ∞]` 型の拡張実数，limsup/liminf など |

名前だけ見ると似ていますが，これらは別々の型です．
型が違うものを混ぜるときは，coercion や `toReal`，`ofReal`，`toNNReal` などの変換を確認します．
特に，`toReal` や `ofReal` には情報を失うものがあります．

```lean
#check Real
#check ℝ
#check NNReal
#check ℝ≥0
#check ENNReal
#check ℝ≥0∞
#check EReal

#synth Field ℝ
#synth LinearOrder ℝ
#synth IsStrictOrderedRing ℝ
#synth Archimedean ℝ
#synth TopologicalSpace ℝ
#synth CompleteSpace ℝ
#synth ConditionallyCompleteLinearOrder ℝ

#synth LinearOrderedCommGroupWithZero ℝ≥0
#synth ConditionallyCompleteLinearOrderBot ℝ≥0
#synth CompleteLinearOrder ℝ≥0∞
#synth CompleteLinearOrder EReal

#check Real.equivCauchy
#check Real.sqrt
#check Real.sqrt_sq_eq_abs

example : ((3 : Nat) : ℝ) + 2 = 5 := by
  norm_num

example (x : ℝ) : 0 ≤ |x| := by
  exact abs_nonneg x

example (x : ℝ) : Real.sqrt (x ^ 2) = |x| := by
  simpa using Real.sqrt_sq_eq_abs x
```

`norm_num` は数値計算に強い tactic です．
実数上の具体的な数値等式・不等式を閉じるときによく使います．
`Real.sqrt` のような標準関数も `Real` 名前空間に置かれ，補題名も `Real.sqrt_sq_eq_abs` のように整理されています．

### `NNReal`: 非負実数

`NNReal` は nonnegative real，つまり $[0, \infty)$ に対応する型です．
記法は `ℝ≥0` です．
実装は `ℝ` の subtype で，

```lean title="Mathlib.Data.NNReal.Defs"
def NNReal := { r : ℝ // 0 ≤ r }
```

です．
要素は実数 `r` と証明 `0 ≤ r` の組ですが，通常は coercion により実数としても使えます．
`NNReal.mk x hx` は，非負性の証明 `hx : 0 ≤ x` から `x : ℝ≥0` を作るコンストラクタです．
一方，`Real.toNNReal x` は任意の実数を非負実数に送りますが，負の値は `0` に潰します．
したがってこれは単なる型変換ではありません．

```lean
#check NNReal.mk
#check NNReal.toReal
#check Real.toNNReal
#check Real.coe_toNNReal
#check Real.toNNReal_of_nonpos

example (x : ℝ≥0) : (0 : ℝ) ≤ (x : ℝ) := by
  exact x.property

example (x : ℝ) (hx : 0 ≤ x) : ((Real.toNNReal x : ℝ≥0) : ℝ) = x := by
  exact Real.coe_toNNReal x hx

example : ((Real.toNNReal (-3 : ℝ) : ℝ≥0) : ℝ) = 0 := by
  norm_num [Real.toNNReal]
```

`ℝ≥0` は非負性を型に持たせたいときに便利です．
たとえば距離，ノルム，確率，非負関数などは，値が常に非負であることを命題として毎回仮定するより，値域を `ℝ≥0` にすると扱いやすくなります．
ただし，`ℝ≥0` は体ではありません．
負数を持たないので，通常の `ℝ` と同じ引き算・反数の感覚で使うと詰まります．

### `ENNReal`: 拡張非負実数

`ENNReal` は extended nonnegative real，つまり $[0, \infty]$ に対応する型です．
記法は `ℝ≥0∞` で，実装は `WithTop ℝ≥0` です．
これは `ℝ≥0` に新しい最大元 `∞` を付け加えた型です．

測度論では，測度や非負関数の積分値が `∞` になりうるため，`ENNReal` がよく現れます．
また，拡張距離 `edist` の値域としても使われます．
`ENNReal` には `∞` があるため，`toReal` は `∞` を `0` に送ります．
また，`ENNReal.ofReal` は負の実数を `0` に送ります．
したがって，`toReal` と `ofReal` は情報を失う変換です．

```lean
#check ENNReal.ofReal
#check ENNReal.toReal
#check ENNReal.toNNReal
#check ENNReal.ofReal_ne_top
#check ENNReal.toReal_ofReal

example : (0 : ℝ≥0∞) ≤ ∞ := by
  simp

example : (∞ : ℝ≥0∞) + 1 = ∞ := by
  simp

example : (1 : ℝ≥0∞) + 2 = 3 := by
  norm_num

example : ENNReal.ofReal (-3 : ℝ) = 0 := by
  norm_num [ENNReal.ofReal, Real.toNNReal]

example (x : ℝ) (hx : 0 ≤ x) : (ENNReal.ofReal x).toReal = x := by
  exact ENNReal.toReal_ofReal hx

example : (∞ : ℝ≥0∞).toReal = 0 := by
  rfl
```

`ENNReal.ofReal x` は常に有限な `ℝ≥0∞` です．
そのため `ENNReal.ofReal_ne_top` のような補題があります．
一方で，`∞` から `ℝ` に戻すと `0` になるので，`toReal` を使うときは有限性の仮定 `a ≠ ∞` が必要になることが多いです．

### `EReal`: 符号つき拡張実数

`EReal` は extended real，つまり $[-\infty, \infty]$ に対応する型です．
実装は `WithBot (WithTop ℝ)` で，`ℝ` に上端 `⊤` と下端 `⊥` を追加したものです．
`ENNReal` が非負側だけを拡張するのに対し，`EReal` は正負両方向に無限大を持ちます．

`EReal` は完備線形順序として扱えるため，順序論的な上限・下限や limsup/liminf のように，正負の無限大が自然に出る場面で使います．
ただし，代数演算には通常の実数とは違う注意点があります．
たとえば `EReal.toReal` も `⊤` と `⊥` を `0` に送ります．

```lean
#check EReal
#check EReal.toReal
#check EReal.toReal_top
#check EReal.toReal_bot
#check EReal.toReal_coe

example : EReal.toReal (⊤ : EReal) = 0 := by
  exact EReal.toReal_top

example : EReal.toReal (⊥ : EReal) = 0 := by
  exact EReal.toReal_bot

example (x : ℝ) : EReal.toReal (x : EReal) = x := by
  exact EReal.toReal_coe x
```

まとめると，通常の実解析ではまず `ℝ` を使います．
値が非負であることを型に持たせたいなら `ℝ≥0`，非負で `∞` も許したいなら `ℝ≥0∞`，正負両方の無限大を許したいなら `EReal` を使います．
変換関数の名前を見たら，それが埋め込みなのか，負の値や無限大を `0` に潰す写像なのかを確認するのが重要です．

---
## bundled structure，morphism，subobject

Mathlib では，数学的対象を構造体として束ねることがよくあります．
たとえば準同型は，単なる関数ではなく「関数本体」と「演算を保つ証明」を持つ構造体です．
これを bundled structure と呼ぶことがあります．
bundled にすると，写像そのものと構造保存の証明を 1 つの対象として渡せるため，定理の仮定や合成の記述が整理されます．

```lean
#check MonoidHom
#check RingHom
#check MonoidHom.map_one
#check map_add

example : (RingHom.id ℤ) 3 = 3 := by
  rfl

example (f : ℤ →+* ℤ) (x y : ℤ) : f (x + y) = f x + f y := by
  exact map_add f x y
```

`ℤ →+* ℤ` は，整数環から整数環への環準同型です．
`map_add` は，加法を保つことを表す典型的な補題名です．
Mathlib では，`map_zero`，`map_one`，`map_mul`，`map_add` のように，写像が構造を保つ定理が統一的な名前で用意されています．
準同型 `f : ℤ →+* ℤ` は関数のように `f x` と適用できますが，内部的には関数だけでなく保存性の証明も持っています．

部分構造も bundled な対象として扱われます．
たとえば線形代数では `Submodule R M`，代数では `Subgroup G` や `Subsemiring R`，位相では部分空間に関する構造が現れます．
各論は次章以降で扱いますが，ここでは名前だけ確認しておきます．

```lean
#check Submodule
#check Subgroup
#check Subsemiring
```

---
## coercion と subtype

Mathlib では，自然な埋め込みは coercion として登録されています．
たとえば自然数を実数として使うとき，`((3 : Nat) : ℝ)` のように型を変換します．
coercion は便利ですが，エラーメッセージを読むときには「Lean がどの型からどの型へ自動変換したのか」を意識する必要があります．

```lean
example : ((3 : Nat) : ℝ) = 3 := by
  norm_num
```

`Subtype` は，条件を満たす要素を集めた型です．
`{n : Nat // 0 < n}` は，正の自然数とその証明を組にした型です．
値を元の型に戻すときは coercion が働きます．
`x.property` は，`x` が subtype の条件を満たすことの証明です．

```lean
example (x : {n : Nat // 0 < n}) : 0 < (x : Nat) := by
  exact x.property

example (x : {n : Nat // 0 < n}) : (x : Nat) ∈ {n : Nat | 0 < n} := by
  exact x.property
```

集合や部分構造の外延性には `ext` を使うことが多いです．
次の例では，集合の等式を元ごとの同値性に変えています．

```lean
example (A B : Set Nat) : A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]
```

---
## 不等式の型と証明パターン

数学では $a \le b$ を 1 つの文として読みます．
Lean でも同じく，`a ≤ b` は命題です．
より正確には，`a b : α` のとき，`a ≤ b` は `Prop` 型の項です．
`≤` という記法は `LE.le` に対応し，`<` は `LT.lt` に対応します．
したがって，不等式は実数専用の構文ではありません．
どの型 `α` の上の順序を使っているかによって，不等式の意味が決まります．

順序の基本性質は型クラスで与えられます．
推移律などを使うには `Preorder α`，反対称性も使うには `PartialOrder α`，任意の 2 元が比較できることを使うには `LinearOrder α` が必要です．
さらに，足し算や掛け算と順序の相性を使うには，`IsOrderedAddMonoid`，`IsOrderedRing`，`IsStrictOrderedRing` などの構造が関わります．
たとえば実数 `ℝ` には線形順序，体，順序環の構造が入っているので，通常の不等式計算ができます．

```lean
#check LE.le
#check LT.lt
#check Preorder
#check PartialOrder
#check LinearOrder
#check IsOrderedAddMonoid
#check IsOrderedRing
#check IsStrictOrderedRing

#check ((3 : ℝ) ≤ 5)
#check ((3 : ℝ) < 5)

#synth LE ℝ
#synth LT ℝ
#synth LinearOrder ℝ
#synth IsOrderedAddMonoid ℝ
#synth IsStrictOrderedRing ℝ
```

`≤` や `<` は型によって意味が変わります．
たとえば `ℝ` 上の `0 ≤ x` と，`ℝ≥0` 上の `0 ≤ x` は見た目が似ていますが，別々の型の上の順序です．
`x : ℝ≥0` は内部的には非負実数なので，実数へ coercion すれば `0 ≤ (x : ℝ)` が取り出せます．

```lean
#check (fun x : ℝ => 0 ≤ x)
#check (fun x : ℝ≥0 => (0 : ℝ) ≤ (x : ℝ))
#check (fun x : ℝ≥0 => (0 : ℝ≥0) ≤ x)

example (x : ℝ≥0) : (0 : ℝ) ≤ (x : ℝ) := by
  exact x.property
```

また，`≤` は数値の大小だけでなく，順序一般を表す記号です．
集合や部分構造では，`≤` が包含関係を表すことがあります．
証明中に不等号が現れたら，まず両辺の型を確認するのが安全です．

```lean
#check (fun s t : Set ℝ => s ≤ t)
#check (fun s t : Set ℝ => s ⊆ t)
#check (fun S T : AddSubgroup ℤ => S ≤ T)
```

不等式の基本的な証明は，推移律や変形補題を使って進めます．
数学で「`a ≤ b ≤ c` だから `a ≤ c`」と書く部分は，Lean では `le_trans` や `calc` で表せます．

```lean
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  exact le_trans h₁ h₂

example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  exact lt_of_lt_of_le h₁ h₂

example (a b : ℝ) (h : a < b) : ¬ b ≤ a := by
  exact not_le_of_gt h

example (a b c d : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d :=
  calc
    a ≤ b := hab
    _ ≤ c := hbc
    _ ≤ d := hcd
```

数値だけの不等式は `norm_num` が得意です．
仮定を含む一次不等式は `linarith` が強く，二次式などの多項式不等式は `nlinarith` が有効なことがあります．
`nlinarith` は，平方非負性のような補助補題を渡すと使いやすくなります．

```lean
example : (3 : ℝ) / 2 < 2 := by
  norm_num

example (x y : ℝ) (hx : x ≤ 3) (hy : y ≤ 4) : x + y ≤ 7 := by
  linarith

example (x : ℝ) : 0 ≤ x ^ 2 := by
  nlinarith [sq_nonneg x]

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  nlinarith [sq_nonneg x]
```

非負性を積み上げる証明では，既存補題を直接使うのが読みやすいことも多いです．
`mul_nonneg` は「非負数同士の積は非負」，`mul_le_mul_of_nonneg_left` は「非負数を左から掛けても不等式の向きは変わらない」という補題です．
補題名では，`le` が `≤`，`lt` が `<`，`nonneg` が `0 ≤ ...`，`pos` が `0 < ...` を表すことが多いです．

```lean
#check add_le_add
#check mul_nonneg
#check mul_le_mul_of_nonneg_left
#check abs_nonneg
#check sq_nonneg

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  exact add_le_add hab hcd

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  exact mul_nonneg hx hy

example (x y c : ℝ) (hxy : x ≤ y) (hc : 0 ≤ c) : c * x ≤ c * y := by
  exact mul_le_mul_of_nonneg_left hxy hc
```

単調性に従う変形は `gcongr` が便利です．
次の例では，両辺に同じ正の項を足す単調性を使っています．
非負性・正値性を自動で示したいときは `positivity` が役に立つことがあります．

```lean
example (x y : ℝ) (hxy : x ≤ y) : x + 1 ≤ y + 1 := by
  gcongr

example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by
  positivity
```

実際の証明では，次のように切り分けると方針を立てやすくなります．

* 具体的な数値計算なら `norm_num`
* 線形不等式なら `linarith`
* 多項式不等式なら `nlinarith` と `sq_nonneg` など
* 単調性なら `gcongr`，または `add_le_add`，`mul_le_mul_of_nonneg_left` など
* 長い連鎖なら `calc`
* 型が混ざるなら，coercion と変換補題を `#check` で確認する

数学者にとって重要なのは，不等式そのものを「文」ではなく「ある型の上の順序関係から作られた命題」と読むことです．
これが分かると，エラーメッセージに出る型クラス仮定や，`le`，`lt`，`nonneg`，`pos` を含む補題名が読みやすくなります．

---
## Mathlib でよく使う証明パターン

Mathlib を使う証明では，まず既存の補題を探し，`rw`，`simp`，`exact`，`apply`，`ext` などで組み合わせます．
型クラスによって定理が一般化されているため，具体的な型ではなく一般的な構造に対する定理を使うことが多くあります．

ここでは，Core Lean だけで進めた前章から一歩進んで，Mathlib を import した環境でよく使う補助 tactic も扱います．
`by_contra`，`push Not`，`nth_rw`，`conv_lhs`，`aesop`，`norm_num`，`linarith`，`nlinarith`，`positivity`，`gcongr`，`#loogle` などは，実用上よく使われますが，Core Lean だけの最小環境では使えないものがあります．

```lean
example (A B : Set Nat) (x : Nat) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  exact Set.mem_inter_iff x A B

example (A B : Set Nat) (x : Nat) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  exact Set.mem_union x A B

example (a b c : Nat) : a + b + c = a + (b + c) := by
  rw [Nat.add_assoc]

example (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b
```

`simpa using ...` は，既存の補題の形とゴールが少し違うときに便利です．
補題とゴールの両方を `simp` で正規化して一致させます．
Mathlib の証明では，既存補題を `exact` でそのまま使うより，`simpa using` で少し形を整えて使う場面がよくあります．

### `norm_num`: 数値計算

`norm_num` は，具体的な数値等式・不等式を証明する tactic です．
自然数だけでなく，整数，有理数，実数の数値計算にも使えます．

```lean
example : (3 : ℤ) + 4 = 7 := by
  norm_num

example : (3 : ℚ) / 2 + 1 / 2 = 2 := by
  norm_num

example : (3 : ℝ) ^ 2 + 4 ^ 2 = 25 := by
  norm_num
```

### `by_contra` と `push Not`

`by_contra h` は背理法の tactic です．
ゴール `P` を証明するかわりに `h : ¬ P` を仮定し，ゴールを `False` に変えます．
Core Lean では `Classical.byContradiction` を直接使えますが，Mathlib を使う実際の証明では `by_contra` がよく使われます．

```lean
example (P : Prop) (h : ¬¬ P) : P := by
  by_contra hP
  exact h hP
```

`push Not` は，否定を量化子や論理結合子の内側へ押し込む tactic です．
たとえば古典論理のもとで，`¬ ∀ x, P x` は `∃ x, ¬ P x` に変形されます．

```lean
example (P : Nat → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  push Not at h
  exact h
```

### `nth_rw` と `conv_lhs`

`rw` は通常，該当する箇所をまとめて書き換えます．
一部だけを書き換えたいときには，`nth_rw` や `conv` モードを使います．
`nth_rw 1 [h]` は，1 番目に現れる該当箇所だけを書き換えます．

```lean
example (a b c : Nat) (h : a + b = c) : (a + b) + (a + b) = c + (a + b) := by
  nth_rw 1 [h]
```

`conv_lhs` は，等式の左辺に入って書き換えるための省略記法です．
Core Lean の `conv => lhs` と同じ発想ですが，短く書けるため実用上よく使われます．

```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv_lhs =>
    rw [Nat.add_comm a b]
```

### `aesop`

`aesop` は，論理規則や登録された補題を使って探索する自動証明 tactic です．
命題論理，単純な述語論理，コンストラクタによる証明に強く，短い補助目標を閉じるときに便利です．

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  aesop

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  aesop
```

### 検索支援: `exact?`，`rw?`，`#loogle`

`exact?`，`rw?`，`try?` は，現在のゴールを閉じる候補や書き換え候補を提案します．
出力は Lean や Mathlib のバージョンによって変わることがあるため，ここでは実行例として示します．

```lean
example (n : Nat) : n + 0 = n := by
  exact?

example (a b : Nat) : a + b = b + a := by
  rw?

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  try?
```

`#loogle` は，式の形やキーワードから Mathlib の定理を探すためのコマンドです．
環境によっては Loogle サーバへの接続が必要です．

```lean
#loogle "_ + 0 = _"
#loogle Nat.succ
#loogle "commutative"
```

---
## Mathlib の命名規則

Mathlib の名前には強い規則性があります．
命名規則を知っていると，補題を推測したり，検索結果を読むのが楽になります．

基本方針は次の通りです．

* 定理名や証明項は `snake_case`: `add_comm`, `mul_assoc`, `not_le_of_gt`
* 型，命題，構造体，クラスは `UpperCamelCase`: `Finset`, `MonoidHom`, `LinearOrder`
* 通常のデータや関数は `lowerCamelCase`
* 名前空間はドットで表す: `Nat.succ_ne_zero`, `Set.mem_inter_iff`
* 写像が構造を保つ補題は `map_add`, `map_mul`, `map_zero` のような名前になりやすい

ただし，古い名前や歴史的事情による例外もあります．
命名規則は検索の手がかりであって，完全な規格ではありません．

```lean
#check Nat.succ_ne_zero
#check Set.mem_inter_iff
#check Set.mem_union
#check add_comm
#check mul_assoc
#check map_add
```

記号に対応する語もある程度決まっています．
たとえば，`∈` は `mem`，`∩` は `inter`，`∪` は `union`，`≤` は `le`，`<` は `lt`，`↔` は `iff` です．
したがって，集合の所属条件を探すときには `mem_inter` や `mem_union` のような名前を予想できます．

また，定理名では結論が先に来ることがよくあります．
たとえば `not_le_of_gt` は「`>` から `¬ ≤` が従う」と読みます．
この名前は，結論 `not_le` と仮定 `of_gt` に分けて読むと分かりやすくなります．

```lean
#check not_le_of_gt
#check lt_of_le_of_ne
```

命名規則は公式の [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html) に整理されています．
新しい補題名を探すときは，記号を英語名に直し，名前空間と結論の形から推測するのが有効です．

---
## まとめ

Mathlib を使う証明では，具体的な対象だけでなく，それが持つ型クラスインスタンスを意識することが重要です．
`Set α` は型 `α` 上の部分集合全体を表し，`Finset α` は有限集合をデータとして持つ型です．
また，`ℝ`，`ℝ≥0`，`ℝ≥0∞`，`EReal` は別々の型であり，用途に応じて選びます．
それぞれに登録された型クラスインスタンスと，型の間の coercion・変換関数を確認することが重要です．
不等式 `a ≤ b` や `a < b` は，両辺の型に入っている順序構造から作られる命題です．
数値計算，線形不等式，多項式不等式，単調性，型変換を切り分けると，使う tactic や補題を選びやすくなります．

Mathlib の証明は既存補題の組み合わせです．
`#check`，`#synth`，命名規則，`simp`，`rw`，`ext`，`norm_num`，`linarith`，`nlinarith` を使いながら，ゴールに合う補題を探して適用します．

---
## 演習問題

この章の演習では，Mathlib の名前を調べながら既存補題を使う演習をします．
`#check`，`#synth`，`simp`，`rw`，`norm_num`，`ext` を積極的に使ってください．

1. `#synth` で，実数が体・線形順序・狭義順序環の構造を持つことを確認してください．

    ```lean4
    #synth Field ℝ
    #synth LinearOrder ℝ
    #synth IsStrictOrderedRing ℝ
    ```

2. `Set` が部分集合として振る舞うことを，membership と外延性で確認してください．

    ```lean4
    example (n : Nat) : n ∈ smallSet ↔ n < 3 := by
      sorry

    example (s t : Set Nat) : t ∈ Set.powerset s ↔ t ⊆ s := by
      sorry
    ```

3. `Finset.range` の membership を `simp` で証明してください．

    ```lean4
    example : (3 : Nat) ∈ Finset.range 5 := by
      sorry

    example : (5 : Nat) ∉ Finset.range 5 := by
      sorry
    ```

4. `Set.ext` を使って集合の等式を証明してください．

    ```lean4
    example {α : Type} (s t : Set α) : s ∩ t = t ∩ s := by
      -- `ext x`, `constructor`, `intro h` で進める．
      sorry
    ```

5. `Real`，`NNReal`，`ENNReal`，`EReal` の型と変換を確認してください．

    ```lean4
    #check Real
    #check NNReal
    #check ENNReal
    #check EReal
    #synth TopologicalSpace ℝ
    #synth ConditionallyCompleteLinearOrder ℝ
    #synth CompleteLinearOrder ℝ≥0∞
    #synth CompleteLinearOrder EReal

    example (x : ℝ) (hx : 0 ≤ x) :
        ((Real.toNNReal x : ℝ≥0) : ℝ) = x := by
      sorry

    example : ENNReal.ofReal (-3 : ℝ) = 0 := by
      sorry
    ```

6. 不等式の型と証明パターンを確認してください．

    ```lean4
    #check LE.le
    #check LT.lt
    #synth LinearOrder ℝ
    #synth IsStrictOrderedRing ℝ

    example (x y : ℝ) (hx : x ≤ 3) (hy : y ≤ 4) : x + y ≤ 7 := by
      sorry

    example (x : ℝ) : 0 ≤ x ^ 2 := by
      sorry

    example (x y c : ℝ) (hxy : x ≤ y) (hc : 0 ≤ c) : c * x ≤ c * y := by
      sorry
    ```

7. 命名規則を使って，次の補題名を予想し，`#check` で確認してください．

    ```lean4
    #check Set.mem_inter_iff
    #check Set.mem_union
    #check not_le_of_gt
    #check lt_of_le_of_ne
    ```

8. `by_contra` と `push Not` を使って，古典論理の証明を書いてください．

    ```lean4
    example (P : Prop) (h : ¬¬ P) : P := by
      sorry

    example (P : Nat → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
      sorry
    ```

9. `nth_rw` または `conv_lhs` を使って，ゴールの一部だけを書き換えてください．

    ```lean4
    example (a b c : Nat) (h : a + b = c) :
        (a + b) + (a + b) = c + (a + b) := by
      sorry

    example (a b c : Nat) : (a + b) + c = (b + a) + c := by
      sorry
    ```

10. `aesop` で閉じる論理問題を作り，手動証明と比較してください．

    ```lean4
    example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (hP : P) : R := by
      sorry
    ```

11. `Finset` と `Set` の違いを説明したうえで，有限和を計算してください．

    ```lean4
    example : (∑ i ∈ Finset.range 4, i) = 6 := by
      -- `native_decide` または `norm_num` 系を試す．
      sorry
    ```
