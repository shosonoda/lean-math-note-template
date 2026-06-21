# Chapter 02: Lean の基本構文・型・データ構造

この章では，Lean のファイルを読むために必要な基本語彙を整理します．
前章では命題論理・述語論理の証明規則を見ました．
ここでは，それらの証明を書くための「言語としての Lean」を見ます．

扱う内容は次の通りです．

* コマンドと式
* 記法 `notation`
* `Prop`，`Type`，`Sort` と universe
* `namespace`，`open`，`variable`
* 引数に現れる `( )`，`{ }`，`[ ]`
* `def`，`abbrev`，`example`，`theorem`，`lemma`
* 関数 `fun`
* 帰納型 `inductive`，構造体 `structure`
* 型クラス `class`，インスタンス `instance`
* 積，直和型（非交和），`Option`，`List` などのデータ構造
* `if`，`match`，`let`，`do` などの制御構文

Lean では「プログラム」と「証明」は同じ構文で書かれます．
自然数を返す関数も，命題の証明も，どちらも型をもつ項です．
したがって，Lean のファイルを読むときは，まず「いま見ているものは環境に名前を追加するコマンドなのか，それとも型をもつ式なのか」を区別すると見通しがよくなります．

```lean
namespace Chapter02
```

---
## コマンドと式

Lean ファイルはコマンドの列です．
`import`，`def`，`theorem`，`inductive`，`structure`，`class`，`instance` などはコマンドです．
一方，`3`，`3 + 4`，`fun n => n + 1`，`Nat`，`P → Q` などは式です．

式は Lean によって elaboration（精密化）され，型が決まります．
コマンドは式そのものではなく，名前つき定義を追加する，型を確認する，評価する，名前空間に入る，といった操作を環境に対して行います．

たとえば `def` コマンドは，名前つきの定義を環境に追加します．
`#check` は式の型を確認するためのコマンドで，`#eval` は計算できる式を評価するためのコマンドです．

```lean
def typedNat : Nat := 3

def typedString : String := "Lean"

#check typedNat
#check typedString
#check (fun n : Nat => n + 1)
#eval typedNat + 4
```

`typedNat : Nat := 3` は，「`typedNat` という名前を定義し，その型は `Nat`，値は `3` である」と読みます．
型注釈 `: Nat` は省略できることもありますが，講義資料では意図を明示するために書くことが多いです．

```lean
def inferredNat := 10

example : inferredNat = 10 := by
  rfl
```

---
## `notation` （記法定義，糖衣構文）

Lean では，標準的な定義だけでなく，数学に近い記号や専用の構文を定義できます．
たとえば `α → β` は関数型の記法，`P ∧ Q` は `And P Q` の記法，`x ∈ s` は membership の記法です．
このような記法は，内部的には既存の定義や関数を使う式へ展開されます．

小さな記法なら，`notation` や `infix` で定義できます．

```lean
notation "twice(" n ")" => n + n

example : twice(3) = 6 := by
  rfl

infixl:65 " +++ " => Nat.add

example : 2 +++ 3 = 5 := by
  rfl
```

`notation "twice(" n ")" => n + n` は，`twice(3)` という表記を `3 + 3` と読むようにする指定です．
`infixl:65 " +++ " => Nat.add` は，中置記法 `x +++ y` を `Nat.add x y` と読むようにする指定です．
`65` は優先順位，`infixl` の `l` は左結合を表します．

実際の Mathlib では，`ℝ`，`∑`，`∈`，`⊔`，`→+*` など，多くの記法が定義されています．
記法は読みやすさのための糖衣構文なので，分からない記法に出会ったら，まず `#check` で型を確認し，「これはどの定義の別表記か」を調べるのが有効です．
講義資料では別記法を使いますが，必要に応じて元の定義名も併記します．

---
## `Prop`，`Type`，`Sort`

Lean では，命題もデータ型も「型」として扱われます．
ただし，目的に応じて主に次の 3 つの階層を意識します．

* `Prop`: 命題の型です．`P : Prop` の項は，命題 `P` の証明です．
* `Type`: 通常のデータ型の型です．`Nat : Type`，`String : Type`，`List Nat : Type` などです．
* `Sort`: `Prop` と `Type` をまとめて扱う，より一般的な階層です．

関係を大まかに書くと，`Sort 0` は `Prop`，`Sort (u + 1)` は `Type u` です．
`Type` とだけ書くと，通常は `Type 0` の意味です．
`#check Type` の結果が `Type : Type 1` となるように，型そのものにも 1 つ上の階層の型があります．

```lean
#check Prop
#check Type
#check Type 1
#check Sort 0
#check Sort 1
```

`Prop` は命題を書くために使います．
次の `IsEvenNat n` は，「自然数 `n` が偶数である」という命題です．
これは真偽値 `Bool` を返す判定関数ではなく，証明すべき命題を返す述語です．

```lean
def IsEvenNat (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

example : IsEvenNat 4 := by
  unfold IsEvenNat
  exact ⟨2, rfl⟩
```

`Type` はデータを分類する型です．
たとえば `Nat` は自然数の型，`List Nat` は自然数のリストの型です．

```lean
def sampleNumber : Nat := 42

def sampleList : List Nat := [1, 2, 3]

example : sampleList.length = 3 := by
  rfl
```

`Sort` を使うと，命題 `Prop` とデータ型 `Type` の両方に対して同じ関数を書けます．
ただし，最初は `Prop` と `Type` を使い分けられれば十分です．
Mathlib の一般的な定義では `Sort u` が現れることがありますが，通常の数学的対象を定義するときは `Type u`，命題を書くときは `Prop` を使う，と覚えておけば十分です．

```lean
universe u v

def idSort (α : Sort u) (x : α) : α :=
  x

example : idSort Nat 7 = 7 := by
  rfl

example (P : Prop) (h : P) : idSort P h = h := by
  rfl
```

---
## 単純型と依存型

型の使い方には，大きく分けて「単純型」と「依存型」があります．
単純型では，関数の返り値の型が入力の値に依存しません．
たとえば `Nat → Nat` は，自然数を受け取って自然数を返す型です．
`α → β` は，返り値の型 `β` が入力値に依存しない関数型です．

```lean
def simpleTypedFunction : Nat → Nat :=
  fun n => n + 1

example : simpleTypedFunction 4 = 5 := by
  rfl
```

一方，依存型では，返り値の型が入力の値に依存します．
典型例は `∀ n : Nat, Fin (n + 1)` のような型です．
`Fin (n + 1)` は `0, 1, ..., n` までの有限型なので，入力 `n` に応じて返り値の型そのものが変わります．
このような依存関数型は，Lean では `∀ n : Nat, ...` という記法で書きます．
結論が `Prop` のときは全称命題として，結論が `Type` のときは値に依存する関数型として読むとよいです．

```lean
def zeroFin (n : Nat) : Fin (n + 1) :=
  ⟨0, Nat.succ_pos n⟩

example : (zeroFin 5).val = 0 := by
  rfl
```

命題も依存型として読むことができます．
`∀ n : Nat, IsEvenNat (2 * n)` は，各自然数 `n` に対して命題 `IsEvenNat (2 * n)` の証明を返す関数型です．
この見方が，Lean で「全称命題の証明を関数のように適用する」理由です．

```lean
theorem twice_is_even (n : Nat) : IsEvenNat (2 * n) := by
  unfold IsEvenNat
  exact ⟨n, rfl⟩

example : IsEvenNat (2 * 7) := by
  exact twice_is_even 7
```

数学の言葉では，依存型は「添字づけられた型の族」を扱う仕組みです．
たとえば `Fin n` は `n` によって大きさが変わる型の族で，`IsEvenNat n` は `n` によって内容が変わる命題の族です．

---
## universe

`universe u v` は，型の階層を表す universe 変数 `u` と `v` を導入するコマンドです．
`Type : Type` としてしまうと自己言及的な矛盾が起こるため，Lean では
`Type 0 : Type 1`，`Type 1 : Type 2`，... という階層を使います．

通常の数学の形式化では universe を意識しなくても進められます．
しかし，任意の型 `α : Type u` について動く定義を書くときには，universe 多相性が現れます．
たとえば `List Nat : Type` と `Type : Type 1` は属する階層が異なります．
`Type u` と書くことで，特定の階層に固定しない定義を書けます．

```lean
def idType (α : Type u) (x : α) : α :=
  x

example : idType Nat 5 = 5 := by
  rfl

example : idType (List Nat) [1, 2] = [1, 2] := by
  rfl
```

`idType` は `Nat` でも `List Nat` でも使えます．
これは，`α` が特定の型ではなく，任意の universe に属する型として書かれているためです．
この章では universe 変数 `u` を明示していますが，Lean が自動的に universe を推論してくれる場面も多くあります．

---
## `variable` とローカルコンテキスト

`variable` コマンドは，以降の定義や定理で使う変数をまとめて宣言します．
これは前章の証明図に出てきた `Γ`，つまり「現在使ってよい変数や仮定の集まり」に対応します．

`section ... end` で囲むと，その中だけで有効な変数を宣言できます．
宣言された変数は，後続の定義で実際に使われたとき，その定義の引数として自動的に追加されます．
たとえば次の `pairFromVariables` は，内部的には `α`，`x`，`y` を引数にもつ定義として扱われます．

```lean
section VariableExamples

variable (α : Type u)
variable (x y : α)

def pairFromVariables : α × α :=
  (x, y)

example : pairFromVariables Nat 2 5 = (2, 5) := by
  rfl

end VariableExamples
```

波括弧 `{α : Type u}` で宣言した引数は，Lean が推論できる場合には省略できる暗黙引数になります．
丸括弧 `(α : Type u)` は通常の明示的な引数，波括弧 `{α : Type u}` は暗黙引数です．
次の `singletonList 3` では，要素 `3` の型から `α = Nat` が推論されます．

```lean
section ImplicitVariableExamples

variable {α : Type u}

def singletonList (x : α) : List α :=
  [x]

example : singletonList 3 = [3] := by
  rfl

example : singletonList "a" = ["a"] := by
  rfl

end ImplicitVariableExamples
```

### 引数に現れる `( )`，`{ }`，`[ ]`

Lean の定義や定理では，引数の括弧に意味があります．
Mathlib の定理を読むときに重要なので，ここで整理しておきます．

* `(x : α)`: 明示的な引数です．通常，関数や定理を使う側が値を与えます．
* `{α : Type u}`: 暗黙引数です．Lean が周囲の式から推論できるなら，通常は書きません．
* `[Add α]`: 型クラス引数です．Lean が登録済みの `instance` から自動的に探します．

たとえば `(h : P)` は「命題 `P` の証明 `h` を明示的な引数として受け取る」という意味です．
一方，`{α : Type u}` は命題の仮定ではなく，推論される型パラメータです．
`[Add α]` も通常の変数というより，「`α` には足し算がある」という構造を型クラス探索で要求している，と読みます．

```lean
def explicitId (α : Type u) (x : α) : α :=
  x

def implicitId {α : Type u} (x : α) : α :=
  x

def addWithClass {α : Type u} [Add α] (x y : α) : α :=
  x + y

#check explicitId
#check implicitId
#check @implicitId
#check addWithClass

example : explicitId Nat 3 = 3 := by
  rfl

example : implicitId 3 = 3 := by
  rfl

example : addWithClass 2 5 = 7 := by
  rfl
```

暗黙引数を明示したいときは，名前付き引数 `(α := Nat)` を使うことがあります．
また，`@implicitId` のように名前の前に `@` を付けると，通常は隠れている暗黙引数も含めた型を確認できます．

```lean4
#check @implicitId
#check implicitId (α := Nat)
```

最初は「丸括弧は普通に渡す，引数」，「波括弧は Lean が推論する，引数」，「角括弧は型クラス探索で探す，構造」と覚えておけば十分です．

---
## `namespace` と `open`

`namespace` は，名前を整理するためのコマンドです．
大きなプロジェクトでは，同じような名前の定義がたくさん出てきます．
名前空間を使うと，`Geometry.Point` のように，どの分野・モジュールの名前かを明示できます．

```lean
namespace Geometry

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq

def origin : Point :=
  { x := 0, y := 0 }

def reflectX (p : Point) : Point :=
  { x := p.x, y := -p.y }

example : reflectX origin = origin := by
  rfl

end Geometry
```

名前空間の外から参照するときは，完全な名前 `Geometry.Point` や `Geometry.origin` を使います．
このファイル全体は `namespace Chapter02` の中にあるので，厳密な完全名は `Chapter02.Geometry.Point` です．
ただし，同じ `Chapter02` 名前空間の中では `Geometry.Point` と書けます．

```lean
example : Geometry.Point :=
  Geometry.origin

example : Geometry.reflectX Geometry.origin = Geometry.origin := by
  rfl
```

`open` は，名前空間の中の名前を短く使えるようにするコマンドです．
`open Geometry` と書くと，そのスコープ内では `Geometry.Point` を `Point`，`Geometry.origin` を `origin` と書けます．
ただし，読み手にとって由来が分かりにくくなることもあるので，必要な範囲に限定して使うのがよいです．

```lean
section OpenExamples

open Geometry

def reflectedOrigin : Point :=
  reflectX origin

example : reflectedOrigin = origin := by
  rfl

end OpenExamples
```

`namespace ... end` は新しい名前空間に入る構文で，そこで定義した名前はその名前空間に属します．
一方，`open` は既存の名前空間を開いて，名前を短く参照するための構文です．
つまり，`namespace` は名前を作る場所を決め，`open` は名前を読むときの省略を許す，と考えるとよいです．

---
## `def`

`def` は計算内容をもつ定義を作るコマンドです．
関数，値，命題の略記などを定義できます．

```lean
def addTwo (n : Nat) : Nat :=
  n + 2

example : addTwo 3 = 5 := by
  rfl

def IsPositiveNat (n : Nat) : Prop :=
  0 < n

example : IsPositiveNat 3 := by
  unfold IsPositiveNat
  decide
```

`def` で定義した名前は，必要に応じて展開されます．
`rfl` で証明できる等式は，定義を展開して両辺が同じ形になる等式です．
この「定義を展開して同じになる」という同一性を，定義的等しさと呼びます．
`def` で関数を定義すると，その計算規則を `rfl` や `simp` が利用できることがあります．

```lean
example : addTwo 0 = 2 := by
  rfl
```

---
## `abbrev`

`abbrev` は略記を作るコマンドです．
`def` と似ていますが，「新しい概念を作る」というより「長い型や式に短い名前をつける」という意図を表します．
Lean は `abbrev` を展開しやすい略記として扱うので，型の同一視や型推論で邪魔になりにくいです．
一方で，数学的に意味のある新しい概念や，後で定理を付けたい対象には `def` を使うことが多いです．

```lean
abbrev NatPair := Nat × Nat

def sumNatPair (p : NatPair) : Nat :=
  p.1 + p.2

example : sumNatPair (2, 3) = 5 := by
  rfl
```

`NatPair` は `Nat × Nat` の略記なので，Lean は両者をほとんど同じものとして扱います．
このため，`Nat × Nat` 型の値をそのまま `NatPair` として使えます．

```lean
example (p : Nat × Nat) : NatPair := p
```

---
## `fun`

`fun x => t` は無名関数を作る式です．
数学の記法では（関数名を明記しない） $x \mapsto t$ に対応します．
Lean の多引数関数は基本的にカリー化されています．
たとえば `Nat → Nat → Nat` は，自然数を 1 つ受け取って，さらに `Nat → Nat` 型の関数を返す型として読めます．

```lean
def addConst (k : Nat) : Nat → Nat :=
  fun n => n + k

example : addConst 4 3 = 7 := by
  rfl

def applyTwice (f : Nat → Nat) (n : Nat) : Nat :=
  f (f n)

example : applyTwice (fun n => n + 1) 10 = 12 := by
  rfl
```

`fun` はタクティックではなく式です．
そのため，関数を引数に取る関数へ，その場で関数を渡すときによく使います．

---
## `example`，`theorem`，`lemma`

`example` は名前を残さない匿名の宣言です．
構文やタクティックの小さな実験に向いています．
証明の文脈では `example : P := ...` は「命題 `P` の証明をその場で与える」という意味です．
ただし Lean のコマンドとしての `example` は，命題に限らず任意の型の項を匿名で確認する用途にも使えます．

```lean
example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

example : Nat :=
  42
```

命題そのものも式です．
次の最初の例では，`2 + 2 = 4` という命題が `Prop` 型の式であることを示しています．
次の例では，その命題の証明を与えています．

```lean
example : Prop :=
  2 + 2 = 4

example : 2 + 2 = 4 := by
  rfl
```

`theorem` は名前つきの定理を宣言します．
後からその名前を使って参照できます．
`theorem` で定義されるものも，型が `Prop` である項，つまり証明です．
`theorem` や `lemma` の型は命題でなければなりません．
データや計算内容を名前つきで定義したいときは `def` を使います．

```lean
theorem add_zero_named (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

theorem two_plus_two_is_four : 2 + 2 = 4 := by
  rfl

example : 5 + 0 = 5 := by
  exact add_zero_named 5

example : 2 + 2 = 4 := by
  exact two_plus_two_is_four
```

実用上は，補助的な定理を「lemma」と呼ぶことがよくあります．
Core Lean では，補助的な定理も `theorem` で宣言できます．
Mathlib を import している環境では `lemma` というコマンドもよく使われますが，ここでは Core Lean に合わせて `theorem` で書きます．

```lean
theorem zero_add_named (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

example : 0 + 5 = 5 := by
  exact zero_add_named 5

theorem even_four : IsEvenNat 4 := by
  unfold IsEvenNat
  exact ⟨2, rfl⟩

example : IsEvenNat 4 := by
  exact even_four
```

`example`，`theorem`，`lemma` はいずれも，命題を証明するためのコマンドです．
ただし，`example` は上で見たように，匿名の型検査例にも使えます．
命題証明として使う場合の違いは，主に「名前を残すか」「数学的にどのような位置づけか」です．

`def` との関係も重要です．
Lean の内部では，定義も定理も「名前に型つきの項を結びつける」という点では似ています．
たとえば `def` で `Nat` 型の値を定義することも，`Prop` 型の証明を定義することもできます．
ただし，数学的な命題の証明には，意図が明確になるように `theorem` や `lemma` を使うのが普通です．

```lean
def proofByDef : 1 + 1 = 2 := by
  rfl

example : 1 + 1 = 2 := by
  exact proofByDef
```

---
## 代表的なデータ構造

Lean には基本的なデータ構造が用意されています．
数学の形式化でも，タプル，直和型（非交和），オプション，リストは頻繁に使います．

### 積 `α × β`

`α × β` は 2 つのデータを組にする型です．
`p.1` で第 1 成分，`p.2` で第 2 成分を取り出します．
命題論理の連言 `P ∧ Q` と形は似ていますが，`α × β` はデータ型の積，`P ∧ Q` は命題の連言です．

```lean
def sampleProduct : Nat × String :=
  (3, "three")

example : sampleProduct.1 = 3 := by
  rfl

example : sampleProduct.2 = "three" := by
  rfl
```

3 つの積は，Lean では右結合として読まれます．
つまり `α × β × γ` は `α × (β × γ)` の略記です．
そのため，`p : α × β × γ` から第 1 成分を取り出すには `p.1`，第 2 成分を取り出すには `p.2.1`，第 3 成分を取り出すには `p.2.2` と書きます．

```lean
def sampleTriple : Nat × String × Bool :=
  (3, "three", true)

example : sampleTriple.1 = 3 := by
  rfl

example : sampleTriple.2.1 = "three" := by
  rfl

example : sampleTriple.2.2 = true := by
  rfl
```

括弧を明示すると，構造が分かりやすくなります．
`(3, "three", true)` は `(3, ("three", true))` と同じ形です．

```lean
example : sampleTriple = (3, ("three", true)) := by
  rfl
```

### 直和型（非交和） `α ⊕ β`

`α ⊕ β` は，左の型 `α` の値または右の型 `β` の値をもつ型です．
左側の値は `Sum.inl`，右側の値は `Sum.inr` で作ります．
命題の選言 `P ∨ Q` と似ていますが，`α ⊕ β` はデータを入れるための直和型です．
集合論でいう非交和，あるいはタグ付き和に対応します．
たとえば `α` と `β` に同じ値のように見える要素があっても，`Sum.inl a` と `Sum.inr b` は左由来か右由来かをタグで区別します．

記号に注意します．
Lean で `α ⊕ β` と書くと `Sum α β` の記法です．
一方，数学で非交和に使われることがある `α ⊔ β` は，Lean では `Sum` の記法ではありません．
Mathlib では `⊔` は束の上限・join を表す記号として使われ，たとえば集合の合併や部分群・部分空間の上限のような場面に現れます．
したがって，型 `α` と `β` の非交和を表したいときは `α ⊕ β`，または明示的に `Sum α β` と書きます．

```lean
def sumLeft : Nat ⊕ String :=
  Sum.inl 10

def sumRight : Nat ⊕ String :=
  Sum.inr "ten"

def sumToNat (x : Nat ⊕ Bool) : Nat :=
  match x with
  | Sum.inl n => n
  | Sum.inr b => if b then 1 else 0

example : sumToNat (Sum.inl 7) = 7 := by
  rfl

example : sumToNat (Sum.inr true) = 1 := by
  rfl
```

### `Option α`

`Option α` は，値が存在する場合と存在しない場合を表します．
`some x` は値がある場合，`none` は値がない場合です．
部分関数や失敗するかもしれない計算を表すときによく使います．
数学的な存在命題 `∃ x, P x` とは異なり，`Option α` は計算可能なデータとして `α` の値を持つか持たないかを表します．

```lean
def safePred (n : Nat) : Option Nat :=
  match n with
  | 0 => none
  | m + 1 => some m

example : safePred 0 = none := by
  rfl

example : safePred 4 = some 3 := by
  rfl
```

### `List α`

`List α` は有限列です．
`[]` は空リスト，`x :: xs` は先頭に `x` を追加したリストです．
リストは帰納型なので，空リストの場合と `x :: xs` の場合に分けて再帰関数を書けます．

```lean
def listExample : List Nat :=
  [1, 2, 3].map (fun n => n + 1)

example : listExample = [2, 3, 4] := by
  rfl

def headD {α : Type u} (default : α) : List α → α
  | [] => default
  | x :: _ => x

example : headD 0 [5, 6, 7] = 5 := by
  rfl

example : headD 0 ([] : List Nat) = 0 := by
  rfl
```

---
## `inductive`

`inductive` は帰納型を定義するコマンドです．
帰納型は，いくつかのコンストラクタによって値を作る型です．
自然数，リスト，選言，存在量化なども Lean では帰納型として実装されています．
帰納型を使うときは，「値はどのコンストラクタで作られたか」による場合分けと，「小さい構造に対する仮定」を使う帰納法が基本になります．

```lean
inductive Sign where
  | negative
  | zero
  | positive
deriving Repr, DecidableEq

def signNeg : Sign → Sign
  | Sign.negative => Sign.positive
  | Sign.zero => Sign.zero
  | Sign.positive => Sign.negative

example : signNeg Sign.positive = Sign.negative := by
  rfl

example : signNeg Sign.zero = Sign.zero := by
  rfl
```

帰納型は再帰的にも定義できます．
次の `Tree α` は，値をもつ葉と，左右の部分木をもつ節点からなる二分木です．

```lean
inductive Tree (α : Type u) where
  | leaf (value : α)
  | node (left right : Tree α)

def Tree.size {α : Type u} : Tree α → Nat
  | Tree.leaf _ => 1
  | Tree.node left right => Tree.size left + Tree.size right

example : Tree.size (Tree.node (Tree.leaf 1) (Tree.leaf 2)) = 2 := by
  rfl
```

`inductive` で定義した型を使うときは，`match` による場合分けが基本になります．
これは，前章の `∨` や `∃` の除去規則で `cases` を使ったことと同じ発想です．

---
## `structure`

`structure` は，複数のフィールドをもつデータ型を定義するコマンドです．
数学では，点，群，位相空間，線形写像などを構造体として表すことが多くあります．
`structure` は，名前つきフィールドをもつ積型と考えると分かりやすいです．
Mathlib では，代数構造や位相構造の仮定が `structure` や `class` として大量に現れます．

```lean
structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq

def origin : Point :=
  { x := 0, y := 0 }

def Point.swap (p : Point) : Point :=
  { x := p.y, y := p.x }

example : origin.x = 0 := by
  rfl

example : Point.swap { x := 1, y := 2 } = { x := 2, y := 1 } := by
  rfl
```

フィールド名 `x`，`y` は射影関数としても使えます．
`p.x` は「点 `p` の `x` 成分」です．

```lean
def addPoint (p q : Point) : Point :=
  { x := p.x + q.x, y := p.y + q.y }

example : addPoint { x := 1, y := 2 } { x := 3, y := 4 } = { x := 4, y := 6 } := by
  rfl
```

---
## 型クラス `class` と `instance`

型クラスは，「この型にはこの構造や操作がある」という情報を Lean に登録する仕組みです．
`class` は型クラスを定義するコマンド，`instance` は特定の型がその型クラスの実例であることを登録するコマンドです．
ここでの「実例」は，命題の例ではなく，型クラスのフィールドを実際に埋めた構造体の値です．

Lean の「型クラス」は，オブジェクト指向プログラミングの「クラス」とは違います．
オブジェクト指向のクラスは，データとメソッドをまとめた「オブジェクトの設計図」として使われます．
一方，Lean の型クラスは，ある型に対して必要な構造や操作を自動的に探すための仕組みです．

Lean の `class` は構文上は `structure` に近く，フィールドをもつ構造体として定義されます．
ただし，`class` として定義すると，Lean の型クラス探索が使えるようになります．
つまり，`[Pretty α]` のような引数を見つけたとき，登録済みの `instance` から自動的に適切な値を探します．

たとえば，標準の `Add α` は「`α` には足し算がある」という型クラスです．
ここでは小さな例として，値を文字列化する `Pretty` という型クラスを定義します．
Mathlib では，`Group G`，`TopologicalSpace X`，`NormedRing R` なども型クラスとして現れます．

```lean
class Pretty (α : Type u) where
  pretty : α → String

def pretty {α : Type u} [Pretty α] (x : α) : String :=
  Pretty.pretty x

instance : Pretty Bool where
  pretty b := if b then "true" else "false"

instance : Pretty Nat where
  pretty n := toString n

example : pretty true = "true" := by
  rfl

example : pretty (37 : Nat) = "37" := by
  rfl
```

角括弧 `[Pretty α]` は，「`α` に対する `Pretty` のインスタンスを型クラス探索で探す」という意味です．
一度 `instance` を登録しておくと，Lean が必要な場所で自動的に見つけます．
この仕組みにより，`pretty (some true)` ではまず `Option Bool` の `Pretty` インスタンスが使われ，その内部で `Bool` の `Pretty` インスタンスが使われます．

```lean
instance {α : Type u} [Pretty α] : Pretty (Option α) where
  pretty x :=
    match x with
    | none => "none"
    | some a => "some " ++ pretty a

example : pretty (some true) = "some true" := by
  rfl

example : pretty (none : Option Nat) = "none" := by
  rfl
```

---
## 制御構文

Lean の制御構文は，通常のプログラミング言語の構文に似ています．
ただし Lean では，これらもすべて型をもつ式です．

### `if ... then ... else ...`

`if` は条件分岐です．
条件には，`Bool` または Lean が真偽を判定できる命題が入ります．
`n < 10` は命題ですが，自然数の大小比較には判定手続きがあるため `if` の条件として使えます．
一般の命題 `P : Prop` を条件にするには，Lean が `[Decidable P]` を見つけられる必要があります．

```lean
def sizeLabel (n : Nat) : String :=
  if n < 10 then "small" else "large"

example : sizeLabel 3 = "small" := by
  rfl

example : sizeLabel 20 = "large" := by
  rfl
```

### `match`

`match` は帰納型やデータ構造を場合分けする式です．
`Option`，`List`，自分で定義した `inductive` などを分解できます．
各分岐は同じ型の式を返す必要があります．
証明で使う `cases` はゴールを場合分けする tactic ですが，`match` は式の中で場合分けして値を作る構文です．

```lean
def optionToNat : Option Nat → Nat
  | none => 0
  | some n => n

example : optionToNat none = 0 := by
  rfl

example : optionToNat (some 8) = 8 := by
  rfl

def listLength : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + listLength xs

example : listLength [10, 20, 30] = 3 := by
  rfl
```

### `let`

`let` は局所的な名前をつける構文です．
長い式を読みやすくするために使います．
`let` で導入した名前は，その式の残りの部分だけで使えます．
定義を環境に追加する `def` とは異なり，`let` は局所的な束縛です．

```lean
def squareSum (x y : Nat) : Nat :=
  let x2 := x * x
  let y2 := y * y
  x2 + y2

example : squareSum 3 4 = 25 := by
  rfl
```

### `do`

`do` 記法は，モナド的な計算を順番に書くための構文です．
最初は，失敗するかもしれない計算を `Option` でつなぐ例として見るとよいです．
`do` ブロックの各行も式を組み立てるための記法であり，最終的には `bind` や `pure` を使う式に展開されます．

```lean
def addOptions (x y : Option Nat) : Option Nat := do
  let a ← x
  let b ← y
  pure (a + b)

example : addOptions (some 2) (some 5) = some 7 := by
  rfl

example : addOptions none (some 5) = none := by
  rfl
```

`let a ← x` は，`x` が `some a` なら中身を取り出して続行し，`none` なら全体を `none` にする，という動きをします．
同様に `let b ← y` で `y` が `none` なら，以降の `pure (a + b)` は実行されず，結果は `none` になります．
証明では `do` 記法を頻繁に使うわけではありませんが，Lean でプログラムを書くときには重要です．

---
## まとめ

Lean の基本は「すべての式には型がある」という考え方です．
`Prop` は命題，`Type` はデータ型，`Sort` はその両方を含む一般化です．
`def`，`theorem`，`lemma`，`inductive`，`structure`，`class`，`instance` は，Lean の環境に新しい名前や規則を追加するコマンドです．

今後 Mathlib を読むときには，まず宣言が `def` なのか，`theorem`/`lemma` なのか，`structure` なのか，`class`/`instance` なのかを見ると，対象の役割を把握しやすくなります．
---
## 演習問題

この章の演習では，Lean の式・型・コマンドを読む演習をします．
証明だけでなく，`#check` や `#eval` で結果を確認してください．

1. `#check` で次の式の型を確認してください．

    ```lean4
    #check Nat
    #check (3 : Nat)
    #check fun n : Nat => n + 1
    #check List Nat
    #check Option String
    ```

2. 自然数を 2 倍する関数を `def` で定義し，簡単な計算例を証明してください．

    ```lean4
    def twiceExercise (n : Nat) : Nat :=
      -- ここを埋める．
      sorry

    example : twiceExercise 4 = 8 := by
      -- 定義通りなら `rfl` で閉じる．
      sorry
    ```

3. 2 つの成分を持つ構造体を定義し，フィールドを取り出してください．

    ```lean4
    structure PointExercise where
      x : Nat
      y : Nat

    def pExercise : PointExercise :=
      { x := 2, y := 5 }

    example : pExercise.x = 2 := by
      sorry
    ```

4. `Option Nat` を場合分けする関数を書いてください．

    ```lean4
    def optionDefaultExercise : Option Nat → Nat
      | none => 0
      | some n => -- ここを埋める．
          sorry
    ```

5. 3 つの積 `α × β × γ` から各成分を取り出す式を書いてください．

    ```lean4
    example (α β γ : Type) (x : α × β × γ) : α :=
      -- 第 1 成分
      sorry

    example (α β γ : Type) (x : α × β × γ) : β :=
      -- 第 2 成分
      sorry

    example (α β γ : Type) (x : α × β × γ) : γ :=
      -- 第 3 成分
      sorry
    ```

6. `namespace` を使って，同じ名前の定義が衝突しないことを確認してください．

    ```lean4
    namespace AExercise
    def value : Nat := 10
    end AExercise

    namespace BExercise
    def value : Nat := 20
    end BExercise

    #check AExercise.value
    #check BExercise.value
    ```

7. 型クラスを要求する関数の例として，加法を使う関数を定義してください．

    ```lean4
    def addThreeExercise {α : Type} [Add α] (a b c : α) : α :=
      -- `a + b + c`
      sorry
    ```
