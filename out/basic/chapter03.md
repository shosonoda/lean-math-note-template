# Chapter 03: tactic を用いた証明

この章では，Lean で証明を書くための基本的な道具を整理します．
前章までに，命題，型，定義，構造体，帰納型などを見ました．
ここでは，それらを使って実際に証明を進める方法に焦点を当てます．

特に次の内容を扱います．

* tactic モードの読み方
* `sorry` と未完成の証明
* tactic モードでない証明
* `exact`，`assumption`，`rfl`，`show`，`change`，`dsimp`
* `rw`，`simp`，`simpa`
* tactic 連結子 `<;>`
* `conv` モード
* `apply`，`intro`，`specialize`
* `have`，`suffices`
* `constructor`，`obtain`，`rintro`，`rcases`，`cases`，`left`，`right`
* `by_cases`，`Classical.byContradiction`，`exfalso`，`contradiction`
* `calc` モード
* `congr`，`ext`，`funext`
* Lean における等号の証明パターン
* 命題外延性，選択，商，古典論理
* `induction`
* `decide`，`grind`
* `#check`，`exact?`，`rw?` などの検索支援

`ring`，`nlinarith`，`linarith` などの代数・不等式向け tactic は，次章の Mathlib を使う証明で扱います．

```lean
namespace Chapter03
```

---
## tactic モードの基本

`by` 以降に tactic を並べる書き方を tactic モードと呼びます．
Lean は現在のゴールを持っていて，各 tactic はそのゴールを変形したり閉じたりします．
VS Code の Infoview では，上側にローカルコンテキスト，下側に現在のゴールが表示されます．
tactic を 1 行実行するたびに，Lean は未解決のゴールを更新します．
すべてのゴールが閉じると，`by ...` 全体が証明項になります．

`by` は，`example ... := by` や `theorem ... := by` の直後だけに現れる特別な記号ではありません．
Lean がある場所で型 `T` の項を期待しているとき，そこに

```lean
by
  ...
```

と書くと，Lean は「型 `T` の項を tactic で作る」モードに入ります．
特に `T : Prop` のとき，これは「その場所で必要な証明を tactic で作る」という意味です．

たとえば次の例では，`P ∧ Q` の証明をペア `⟨_, _⟩` として作っています．
左成分には `P` の証明，右成分には `Q` の証明が必要なので，それぞれの成分の位置に `by ...` を直接書けます．

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨by
      exact hP,
    by
      exact hQ⟩
```

後の章で出てくる `⟨2, by norm_num [smallSet]⟩` も同じ使い方です．
subtype の要素を作るには「値」と「その値が条件を満たす証明」が必要なので，2 番目の成分に `by norm_num [smallSet]` と書いて，必要な証明を tactic で作っています．

証明を書いている途中では，`sorry` を一時的な穴として使えます．
`sorry` はどんなゴールも仮に閉じますが，Lean はその宣言に warning を出します．
したがって，演習問題や作業中の証明では便利ですが，完成した定理の証明として残してはいけません．

```lean4
example (P : Prop) : P := by
  sorry
```

このコードは型検査自体は通りますが，「この宣言は `sorry` を使っている」という警告が残ります．
`sorry` は証明探索の道具ではなく，あとで埋めるべき印です．

一番直接的な tactic は `exact` です．
ゴールと同じ型をもつ項や証明をすでに持っているとき，それを `exact` に渡します．
厳密には，ゴールの型と `exact` に渡す項の型が定義的に等しいときに使えます．

```lean
example (P : Prop) (hP : P) : P := by
  exact hP
```

`assumption` は，ローカルコンテキストの中からゴールと一致する仮定を探して使います．

```lean
example (P Q : Prop) (hP : P) (_hQ : Q) : P := by
  assumption
```

`rfl` は，両辺が定義を展開すれば同じになる等式を閉じます．
「計算すれば同じ」という等式によく使います．

```lean
example : (fun n : Nat => n + 1) 2 = 3 := by
  rfl
```

Lean の等式 `a = b` は `Eq a b` という型です．
`rfl` は `Eq.refl`，つまり反射律を使う tactic です．
反射律は本来 `a = a` を証明するものですが，Lean は両辺を計算・定義展開して同じ式になる場合にも `rfl` を受け入れます．
このように，計算や定義展開だけで同じと判定されることを「定義的に等しい」，英語で definitionally equal と言います．

```lean
#check Eq
#check Eq.refl

example : Eq 3 3 := by
  rfl

example : (fun n : Nat => n + 1) 2 = 3 := by
  exact Eq.refl 3
```

一方，数学的には正しい等式でも，定義的に等しくない場合は `rfl` では閉じません．
たとえば `a + b = b + a` は可換性の定理 `Nat.add_comm` を使って証明します．
このような「命題として証明された等式」は，`rw` などで書き換えに使います．

```lean
example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

def Positive (n : Nat) : Prop :=
  0 < n
```

`show` は，現在のゴールを明示的に書く tactic です．
証明を読む人に「いま何を示しているか」を示すのに使えます．
`show` で書いた命題は，現在のゴールと定義的に同じでなければなりません．

```lean
example (n : Nat) : n + 0 = n := by
  show n + 0 = n
  exact Nat.add_zero n
```

`change` は，現在のゴールを定義的に等しい別の表示へ置き換える tactic です．
次の例では，`Positive 3` を定義通り `0 < 3` に変えています．
論理的に同値な任意の命題へ変えられるわけではありません．

```lean
example : Positive 3 := by
  change 0 < 3
  decide
```

`unfold` も定義を展開します．
特定の名前を明示的に展開したいときに使います．

```lean
def double (n : Nat) : Nat :=
  n + n

example : double 4 = 8 := by
  unfold double
  rfl
```

`dsimp` は definitional simplification の略で，定義を展開して計算で簡約できる部分を整理します．
MiL では，関数を値に適用した式や，定義の中に隠れている全称量化を見やすくする場面で使われます．
`simp` と違って，一般の補題による書き換えではなく，主に定義展開と計算による簡約を行います．

```lean
def FnUb (f : Nat → Nat) (a : Nat) : Prop :=
  ∀ x, f x ≤ a

example (f : Nat → Nat) (a : Nat) (h : FnUb f a) : f 0 ≤ a := by
  dsimp [FnUb] at h
  exact h 0
```

---
## tactic モードでない証明

Lean の証明は，必ず tactic モードで書く必要はありません．
証明も項なので，命題の型をもつ式を直接書けば証明になります．
このような書き方を term-style proof，あるいは証明項による証明と呼ぶことがあります．
短い証明では term-style proof の方が構造が見えやすく，長い証明では tactic モードの方が途中状態を確認しやすいことがあります．

```lean
example (P : Prop) (hP : P) : P :=
  hP
```

含意の証明は関数です．
したがって，`P → Q` の証明は `fun hP => ...` という関数として書けます．

```lean
example (P Q : Prop) (hQ : Q) : P → Q :=
  fun _hP => hQ
```

連言の証明は `And.intro` で直接作れます．
tactic モードの `constructor` は，内部的にはこのようなコンストラクタを使う証明に対応しています．

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  And.intro hP hQ
```

山括弧 `⟨...⟩` は，コンストラクタ名を省略して値や証明を作る記法です．
連言，存在命題，subtype，構造体など，「必要な成分を順に与えれば作れる」型でよく使います．
たとえば `P ∧ Q` の証明は `P` の証明と `Q` の証明の組なので，`⟨hP, hQ⟩` と書けます．

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

example : ∃ n : Nat, n + 2 = 5 :=
  ⟨3, rfl⟩

example : {n : Nat // n < 3} :=
  ⟨2, by decide⟩
```

同じ `⟨...⟩` は，後で見る `obtain ⟨hP, hQ⟩ := h` のように，値や証明を分解するパターンとしても使われます．
作る側では「成分を入れる」，分解する側では「成分を取り出す」と読むとよいです．

名前つき定理でも，右辺に証明項を直接書けます．
短い証明では，この書き方の方が読みやすい場合があります．

```lean
theorem term_add_zero (n : Nat) : n + 0 = n :=
  Nat.add_zero n
```

`calc` も tactic ではなく，証明項を作る式です．
そのため，次のように `by` なしで定理の右辺に置けます．

```lean
example (a b c : Nat) : (a + b) + c = b + (a + c) :=
  calc
    (a + b) + c = (b + a) + c := by
      rw [Nat.add_comm a b]
    _ = b + (a + c) := by
      rw [Nat.add_assoc]
```

tactic モードは「ゴールを変形する手続き」として読みやすく，証明項は「証明そのものを式として組み立てる」書き方です．
実際の開発では，短い証明は証明項で書き，長い証明や探索的な証明は tactic モードで書く，という使い分けがよくあります．

---
## `intro` と `apply`

含意 `P → Q` や全称命題 `∀ x, P x` を示すときは，`intro` で仮定や変数を導入します．
ゴールが `P → Q` なら `intro hP` は `hP : P` をローカルコンテキストに追加し，ゴールを `Q` に変えます．
ゴールが `∀ x : α, P x` なら `intro x` は任意の `x : α` を導入し，ゴールを `P x` に変えます．

```lean
example (P Q : Prop) (hQ : Q) : P → Q := by
  intro _hP
  exact hQ

example (P : Nat → Prop) (h : ∀ n : Nat, P n) : P 0 := by
  exact h 0
```

`apply` は，現在のゴールを証明するために使えそうな定理や仮定を適用します．
ゴールが `R` で，`hQR : Q → R` があるとき，`apply hQR` により新しいゴールは `Q` になります．
より一般には，結論が現在のゴールと一致するような定理を後ろ向きに使い，その定理の前提を新しいゴールとして残します．

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  apply hQR
  apply hPQ
  exact hP
```

全称命題を具体的な値に適用したいときは，関数適用のように書けます．
`specialize` は，全称命題の仮定を特定の値に特殊化して，仮定そのものを書き換える tactic です．
次の例では，`h : ∀ n, P n → Q n` が `specialize h 3` によって `h : P 3 → Q 3` に変わります．

```lean
example (P Q : Nat → Prop) (h : ∀ n : Nat, P n → Q n) (hP : P 3) : Q 3 := by
  specialize h 3
  exact h hP
```

---
## `rw`: 等式による書き換え

`rw [h]` は，等式 `h : a = b` を使って，ゴール中の `a` を `b` に書き換えます．
命題の中では，同値 `P ↔ Q` も書き換えに使えます．
`rw` は指定された補題を左から右へ使い，`rw [← h]` と書くと逆向きに使います．

```lean
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]
```

書き換えの向きを逆にしたいときは `←` を使います．

```lean
example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

example (a b : Nat) : b + a = a + b := by
  rw [← Nat.add_comm a b]
```

仮定の中を書き換えるときは `rw [h] at h2` のように `at` を使います．

```lean
example (a b c : Nat) (h : a = b) (h2 : a + c = 10) : b + c = 10 := by
  rw [h] at h2
  exact h2
```

`congr` は，両辺に同じ関数が適用されている等式を，引数の等式に帰着します．
たとえば `f a = f b` を示す問題を `a = b` に変えることができます．
次の例では，残った `a = b` のゴールをローカルコンテキストの `h : a = b` が閉じています．

```lean
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  congr
```

---
## `conv` モード

`conv` モードは，ゴール全体ではなく，式の特定の部分に入り込んで書き換えるためのモードです．
通常の `rw` はゴール全体から書き換え場所を探します．
一方，`conv` では「左辺に入る」「第 1 引数に入る」のように場所を指定してから書き換えます．

```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv =>
    lhs
    rw [Nat.add_comm a b]
```

`conv =>` の中では `lhs` や `rhs` を使って，左辺・右辺を選べます．

```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv =>
    lhs
    arg 1
    rw [Nat.add_comm a b]
```

上の例では，左辺 `(a + b) + c` に入り，さらに第 1 引数 `a + b` に入ってから，そこだけを交換しています．
`arg 1` は関数適用や演算の第 1 引数へ移動する指示です．

```lean
example (a b c : Nat) : (a + b) + (c + 0) = (a + b) + c := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_zero]
```

`conv` の中でも `simp` を使えます．
式の一部だけを簡約したいときに便利です．

```lean
example (a b : Nat) : (fun x : Nat => x + b) a = a + b := by
  conv =>
    lhs
    simp
```

`conv` は強力ですが，構文が細かく，証明が読みにくくなることもあります．
まずは通常の `rw` や `simp` を試し，書き換える場所を厳密に指定したいときに `conv` を使うのがよいです．

---
## `simp` と `simpa`

`simp` は，定義展開，既知の単純化補題，仮定を使った書き換えを組み合わせて，ゴールを単純化します．
日常的に最もよく使う tactic の 1 つです．
`simp` は登録された `[simp]` 補題を，原則として式が単純になる向きに使います．
任意の定理を総当たりで使う tactic ではないので，使ってほしい定義や補題は `simp [name]` の形で明示します．

```lean
example (n : Nat) : n + 0 = n := by
  simp

example (xs : List Nat) : xs ++ [] = xs := by
  simp
```

追加で使いたい定義や補題を `simp [name]` の形で渡せます．

```lean
def addZeroTwice (n : Nat) : Nat :=
  n + 0 + 0

example (n : Nat) : addZeroTwice n = n := by
  simp [addZeroTwice]
```

仮定の中を単純化するときは `simp at h` と書けます．
`simp at *` と書くと，ローカルコンテキストとゴール全体を対象にできますが，証明が読みにくくなる場合もあります．

```lean
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simp at h
  exact h
```

`simpa using h` は，`h` の型と現在のゴールを単純化して一致させます．
最後の一手として非常に便利です．
内部的には「`h` を使う前後で `simp` する」と考えると読みやすいです．

```lean
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simpa using h
```

`simp_all` は，ゴールとローカルコンテキストの仮定をまとめて単純化します．
仮定が多いときに有効です．

```lean
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  simp_all
```

`<;>` は tactic を連結する記法です．
`tac1 <;> tac2` と書くと，まず `tac1` を実行し，その結果生じたすべてのゴールに `tac2` を実行します．
同じ後処理を複数のゴールにまとめて適用したいときに使います．

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption

example (a b : Nat) : a + b = b + a ∧ a + 0 = a := by
  constructor <;> simp [Nat.add_comm]
```

上の 1 つ目は，次の証明を短く書いたものです．

```lean4
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · assumption
  · assumption
```

便利ですが，複雑な証明で乱用すると各ゴールに何が起きたか読みにくくなります．
最初は明示的に箇条書きで証明し，繰り返しが明らかなときだけ `<;>` でまとめるのが無難です．

---
## `have` と `suffices`

`have` は証明の途中で補題を作ります．
長い証明では，途中結果に名前をつけると読みやすくなります．
`have h : Q := ...` と書くと，以降の証明で `h : Q` を仮定として使えます．

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ : Q := hPQ hP
  exact hQR hQ
```

`suffices h : Q` は，「`Q` が示せれば現在のゴールが従う」という形で証明を組み替えます．
先に最終段階を宣言し，あとで十分条件を証明する書き方です．
証明の流れとしては，まず `Q` から元のゴールを導く部分を書き，その後で `Q` 自体を証明します．

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  suffices hQ : Q from hQR hQ
  exact hPQ hP
```

---
## 論理の tactic

連言 `P ∧ Q` や同値 `P ↔ Q` を示すときは，`constructor` がゴールを左右に分けます．
`constructor` は現在のゴールの型のコンストラクタを使って，必要なフィールドや前提をサブゴールとして生成します．

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · intro hP
    exact hPQ hP
  · intro hQ
    exact hQP hQ
```

連言や存在命題を分解するときは `obtain` が便利です．
`obtain ⟨hP, hQ⟩ := h` は，`h` をパターンに従って分解し，得られた成分に名前をつけます．

```lean
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  constructor
  · exact hQ
  · exact hP

example (P : Nat → Prop) (h : ∃ n : Nat, P n) : ∃ n : Nat, P n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩
```

`rintro` は `intro` とパターン分解を同時に行います．
含意の仮定を導入しながら，連言や存在命題をすぐに分解したいときに便利です．

```lean
example (P Q R : Prop) : (P ∧ Q → R) → P → Q → R := by
  rintro h hP hQ
  exact h ⟨hP, hQ⟩
```

`rcases` は，仮定をパターンに従って分解します．
`cases` よりも複雑な入れ子の分解を短く書けます．

```lean
example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : Q ∨ R := by
  rcases h with ⟨_hP, hQ⟩ | hR
  · left
    exact hQ
  · right
    exact hR
```

存在命題を作るには，証拠とその証明を与えます．
`use` は証拠を指定する tactic です．
`use 3` の後，Lean は残りのゴールとして「その証拠が条件を満たすこと」を要求します．
ここでは残ったゴール `3 + 2 = 5` が計算で閉じられます．

```lean
example : ∃ n : Nat, n + 2 = 5 := by
  exact ⟨3, rfl⟩
```

選言 `P ∨ Q` を示すには，`left` または `right` でどちらを示すかを選びます．

```lean
example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

example (P Q : Prop) (hQ : Q) : P ∨ Q := by
  right
  exact hQ
```

選言や帰納型の値を分解するには `cases` を使います．

```lean
example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
      exact hPR hP
  | inr hQ =>
      exact hQR hQ

example (n : Nat) : n = 0 ∨ ∃ k : Nat, n = k + 1 := by
  cases n with
  | zero =>
      left
      rfl
  | succ k =>
      right
      exact ⟨k, rfl⟩
```

`by_cases h : P` は，命題 `P` が成り立つ場合と成り立たない場合に分けます．
一般の命題 `P : Prop` に対する場合分けは，古典論理の排中律に依存します．
`P` が計算で判定可能な命題なら，その判定手続きに基づく場合分けとしても読めます．

```lean
example (P : Prop) : P ∨ ¬ P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h
```

`Classical.byContradiction` は背理法です．
`¬ P → False` から `P` を結論します．
これは一般には古典論理の原理です．
構成的に証明したい場面では，`¬ P` を仮定して `False` を示す「否定の証明」と区別して使います．

```lean
example (P : Prop) (h : ¬¬ P) : P := by
  exact Classical.byContradiction h
```

否定が量化子の外側にある命題を扱うときも，Core Lean だけで証明できます．
たとえば `¬ ∀ n, P n` から `∃ n, ¬ P n` を得るには，古典論理の背理法を使います．
Mathlib では `push Not` がこの種の変形を自動化してくれますが，ここでは明示的に証明します．

```lean
example (P : Nat → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  exact Classical.byContradiction (fun hNoExists =>
    h (fun n =>
      Classical.byContradiction (fun hn =>
        hNoExists ⟨n, hn⟩)))
```

`exfalso` は，現在のゴールを `False` に変えます．
矛盾を導けば任意のゴールが閉じる，という規則を使うための tactic です．
`False.elim` を tactic モードで使いやすくしたものと考えるとよいです．

```lean
example (P Q : Prop) (hP : P) (hNotP : ¬ P) : Q := by
  exfalso
  exact hNotP hP
```

`contradiction` は，コンテキストにある矛盾を探してゴールを閉じます．

```lean
example (P Q : Prop) (hP : P) (hNotP : ¬ P) : Q := by
  contradiction
```

---
## `calc` モード

`calc` は，等式や不等式の連鎖を数学の計算のように書くための構文です．
各行の右側に，そのステップの根拠を書きます．
各ステップは，前の行の右辺と次の行の左辺をつなぐ証明になっている必要があります．

```lean
example (a b c : Nat) : (a + b) + c = b + (a + c) :=
  calc
    (a + b) + c = (b + a) + c := by
      rw [Nat.add_comm a b]
    _ = b + (a + c) := by
      rw [Nat.add_assoc]
```

`calc` は等式だけでなく，推移律を持つ関係にも使えます．
次の例では `≤` の推移律を `calc` が使っています．

```lean
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  calc
    a ≤ b := h₁
    _ ≤ c := h₂
```

tactic モードの中で `calc` を使うこともできます．

```lean
example (a b c : Nat) : (a + b) + c = b + (a + c) := by
  exact
    calc
      (a + b) + c = (b + a) + c := by
        rw [Nat.add_comm a b]
      _ = b + (a + c) := by
        rw [Nat.add_assoc]
```

---
## 関数と構造体: `funext` と `ext`

関数の等式は，すべての入力で値が等しいことを示せば証明できます．
この原理を関数外延性と呼び，Lean では `funext` を使います．

```lean
example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) : f = g := by
  funext x
  exact h x
```

構造体についても，フィールドごとの等式から構造体全体の等式を示すことがあります．
`@[ext]` を付けておくと，`ext` tactic が使う外延性補題が生成されます．

```lean
@[ext]
structure PointForExt where
  x : Nat
  y : Nat

example (p q : PointForExt) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext
  · exact hx
  · exact hy
```

---
## Lean における等号の証明パターン

Lean の等号 `a = b` は `Eq a b` という型です．
つまり「`a = b` を証明する」とは，型 `Eq a b` の証明項を構成することです．
ただし，数学で一言で「等しい」と言うものが，Lean ではいくつかの層に分かれます．

| レベル | 数学での状況 | Lean での姿 | 典型的な証明方法 |
|---|---|---|---|
| 定義的等しさ | 定義から同じ | definitional equality | `rfl`，`change`，`dsimp` |
| 命題的等しさ | 補題や仮定で等しい | propositional equality, `Eq` | `rw`，`calc`，`exact h` |
| 自動化された等式証明 | 正規化すれば同じ | `Eq` の証明を tactic が作る | `simp`，`decide`，`grind` |
| 外延的等しさ | 点ごと・元ごと・成分ごとに同じ | extensional equality | `funext`，`ext` |
| 命題外延性 | 論理的に同値な命題を等しい命題として扱う | propositional extensionality | `propext` |
| 商での等しさ | 同値な代表元を商では同じと見る | quotient equality | `Quot.sound` |

この表のうち，最初の definitional equality だけは Lean の項として直接書く命題ではありません．
これは Lean のカーネルが内部で判断する「計算と定義展開により同じ式である」という関係です．
両辺が定義的に等しければ，`rfl` によって命題的等号 `a = b` の証明を作れます．
逆に，`h : a = b` があるからといって，`a` と `b` が定義的に等しいとは限りません．

```text
definitional equality
  ↓  rfl で Eq の証明を作れる
propositional equality
```

```lean
example : (fun n : Nat => n + 1) 2 = 3 := by
  rfl

example (n : Nat) : n + 0 = n := by
  rfl
```

この環境の自然数の加法では，`n + 0` は定義を展開すると `n` になり，`rfl` で閉じます．

一方，`0 + n = n` は数学的には同じくらい基本的な等式ですが，変数 `n` が具体的に `0` か `Nat.succ k` か分からない状態では計算が進みません．
したがって，これは一般には definitional equality ではなく，定理として証明する propositional equality です．

```lean
example (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

example (n : Nat) : 0 + n = n := by
  simp
```

`simp` で閉じるからといって，その等式が definitional equality であるとは限りません．
`simp` は定義展開だけでなく，`Nat.zero_add` のような単純化補題を使って `Eq` の証明を作ります．
`decide` や `grind` も同様に，判定手続きや推論によって証明を生成する tactic であり，単に `rfl` で閉じているわけではない場合があります．

```lean
example : 3 < 5 := by
  decide
```

交換法則のような等式も，数学的には明らかでも定義を展開するだけでは同じ式になりません．
この場合は，`Nat.add_comm` のような定理を使って `Eq` 型の証明項を構成します．

```lean
example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

example (a b c : Nat) : a + (b + c) = b + (a + c) := by
  calc
    a + (b + c) = (a + b) + c := by
      rw [Nat.add_assoc]
    _ = (b + a) + c := by
      rw [Nat.add_comm a b]
    _ = b + (a + c) := by
      rw [Nat.add_assoc]
```

等式は書き換えにも使います．
`rw [h]` は，証明項 `h : a = b` を使って，ゴール中の `a` を `b` に置き換えます．

```lean
example (a b : Nat) (h : a = b) : a.succ = b.succ := by
  rw [h]

example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

example (a b c : Nat) (h : a = b) : b + c = a + c := by
  rw [← h]
```

同じことを，合同性の補題 `congrArg` を使って証明することもできます．
これは「等しい入力に同じ関数を適用すれば，結果も等しい」という原理です．

```lean
example (a b : Nat) (h : a = b) : a.succ = b.succ := by
  exact congrArg Nat.succ h
```

命題については，`P ↔ Q` と `P = Q` は区別されます．
数学では同値な命題を同一視してよい場面が多いですが，Lean で命題そのものの等式 `P = Q` が必要なときは `propext` を使います．
`P ↔ Q` は「互いに導ける」という命題であり，`P = Q` は `Prop` の元としての命題そのものの等号です．

```lean
#check propext

example (P Q : Prop) (h : P = Q) : P ↔ Q := by
  rw [h]

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h

example (P Q : Prop) : (P ∧ Q) = (Q ∧ P) := by
  apply propext
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩
```

関数の等式では，点ごとの等式から関数そのものの等式を作ります．
数学で「任意の `x` で `f x = g x` だから `f = g`」と言う部分が，Lean では `funext` に対応します．
これは最終的には `f = g` という命題的等号を作っていますが，証明の方法は「点ごとに比べる」という外延的なものです．

```lean
example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) : f = g := by
  funext x
  exact h x

example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) :
    (fun x => f x + 1) = (fun x => g x + 1) := by
  funext x
  rw [h x]
```

関数等号でも，両辺が定義的に同じなら `rfl` で閉じます．
たとえば次の等式は関数の eta 展開が定義的等しさとして扱われる例です．
一方，`fun n => 0 + n` と `fun n => n` は各点で `0 + n = n` を証明する必要があるため，普通は `funext` と `simp` で示します．

```lean
example {α β : Type} (f : α → β) : f = (fun x => f x) := by
  rfl

example : (fun n : Nat => 0 + n) = (fun n : Nat => n) := by
  funext n
  simp
```

構造体でも，同じ構造体の値をフィールドごとに比べて等式を示すことがあります．
これは数学で「成分が等しいので，組や構造体として等しい」と言う部分に対応します．
`@[ext]` を付けておくと，`ext` tactic が使う外延性補題が生成されます．
Mathlib では，集合 `Set` にも外延性補題 `Set.ext` が用意されており，集合の等式を元ごとの同値に変換できます．
集合の具体例は次章の Mathlib の作法で扱います．

```lean
@[ext]
structure PointForEquality where
  x : Nat
  y : Nat

example (p q : PointForEquality) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext
  · exact hx
  · exact hy
```

商型では，同値関係で同値な代表元を，同じ商の元として扱います．
次の例では，自然数を「2 で割った余りが等しい」という関係で割った商を考えています．
`0` と `2` は代表元としては異なりますが，この商の中では等しく，その等式は `Quot.sound` で作られます．

```lean
def SameModTwo (a b : Nat) : Prop :=
  a % 2 = b % 2

example : Quot.mk SameModTwo 0 = Quot.mk SameModTwo 2 := by
  exact Quot.sound (by rfl)
```

少し先の話ですが，型の等号と同型・同値も区別します．
数学では「同型な対象を同じと思う」と言うことがありますが，Lean では `α = β` と `α ≃ β` は別の主張です．
等号 `h : α = β` があれば `cast h` により項を移送できますが，これは同値や同型を与えることとは違います．
定義的等しさ由来の `cast` は計算で消えやすく，`propext`，`funext`，商型などから来る非自明な等号は，証明上は便利でも計算上は扱いが重くなることがあります．

```lean
example (x : Nat) : cast rfl x = x := by
  rfl
```

ここで重要なのは，すべての「等しい」が同じ理由で証明されるわけではない，という点です．
`rfl` は Lean が計算で同じだと分かる等号です．
`rw`，`simp`，`calc` は，補題や仮定から `Eq` の証明を作って使います．
`funext` や `ext` は，点ごと・元ごと・成分ごとの一致から全体の等式を作ります．
`propext` は同値な命題を等しい命題として扱うための原理です．
`Quot.sound` は，同値関係で同値な代表元を商型の中で等しいものとして扱います．

証明が通らないときは，まず「これは定義的等しさで閉じたいのか，補題による等式なのか，外延性で成分ごとに示すべき等式なのか，商の中の等式なのか」を切り分けると，次に使う tactic が選びやすくなります．

---
## 証明項，古典論理，Lean の追加原理

Lean では，命題は型であり，証明はその型の項（ラムダ項，証明項）です．
たとえば `P → Q` の証明は，`P` の証明を受け取って `Q` の証明を返す関数です．
この見方では，「証明する」とは証明項を構成することです．

この型理論の素朴な部分は構成的です．
つまり，一般の命題 `P : Prop` について `P ∨ ¬ P` を証明するには，`P` の証明か `¬ P` の証明のどちらかを実際に与える必要があります．
排中律や背理法，存在からの非構成的な選択を自由に使う標準的な数学を扱うには，追加の原理が必要になります．

Lean の標準的な基礎には，命題外延性，商，選択などの原理が用意されています．
これは Mathlib 独自の仮定ではなく，Lean の上で通常の数学を展開するための基礎です．
Mathlib はその上に多くの定義と定理を積み上げています．

参考:

- Theorem Proving in Lean 4, Axioms and Computation: <https://leanprover.github.io/theorem_proving_in_lean4/Axioms-and-Computation/#axioms-and-computation>
- nLab, choice operator: <https://ncatlab.org/nlab/show/choice+operator>

```lean
#check Classical.em
#check Classical.choice
#check Quot
#check Quot.sound
#check Quot.lift
```

排中律は `Classical.em P` として使えます．
実際の証明では，`by_cases h : P` がよく使われます．
数学で「`P` の場合と `P` でない場合に分ける」と書く部分です．

```lean
example (P : Prop) : P ∨ ¬ P := by
  exact Classical.em P

example (P Q : Prop) (hP : P → Q) (hNotP : ¬ P → Q) : Q := by
  by_cases h : P
  · exact hP h
  · exact hNotP h
```

背理法も標準的な数学では頻繁に使います．
Core Lean では `Classical.byContradiction` がこの役割を持ちます．
次の例は「二重否定から命題を取り出す」古典論理の典型例です．

```lean
example (P : Prop) (h : ¬¬ P) : P := by
  exact Classical.byContradiction h
```

選択は，存在命題から証拠を選ぶときに現れます．
数学では「条件を満たすものを 1 つ取る」と自然に書きますが，Lean でその選んだ値を定義として保存するには `Classical.choose` を使います．
このような定義は一般に計算可能な内容を持たないため，`noncomputable` として宣言します．

ここでいう「選択」は，集合論の選択公理をそのまま Lean に書き写したものではありません．
集合論の選択公理は，非空集合の族から選択関数が存在する，という集合論内部の命題です．
一方，Lean の型理論で使う `Classical.choice` は，型 `α` が空でないという命題 `Nonempty α` の証明から，実際に `α` の項を 1 つ返す選択演算子です．
つまり `Classical.choice : Nonempty α → α` は，証明情報からデータを取り出す追加原理です．
各添字 `i` ごとにこれを使えば，集合論の選択公理に似た選択関数を作れます．
ただし，この関数は計算規則を持たないため，値を定義として保存する場合は `noncomputable` になります．

```lean
noncomputable def choiceFunctionFromNonempty {ι : Type} {α : ι → Type}
    (h : ∀ i : ι, Nonempty (α i)) : (i : ι) → α i :=
  fun i => Classical.choice (h i)

example {ι : Type} {α : ι → Type} (h : ∀ i : ι, Nonempty (α i)) :
    Nonempty ((i : ι) → α i) := by
  exact ⟨choiceFunctionFromNonempty h⟩

noncomputable def chosenNatFromExistence (h : ∃ n : Nat, 10 < n) : Nat :=
  Classical.choose h

example (h : ∃ n : Nat, 10 < n) : 10 < chosenNatFromExistence h := by
  exact Classical.choose_spec h
```

命題外延性 `propext` は，論理的に同値な命題を等しい命題として扱うために使います．
商型は，同値関係で割った対象を作るために使います．
たとえば整数，有理数，剰余類，商群など，標準的な数学では「同値なものを同一視する」構成が頻繁に現れます．

この章で押さえておきたいのは，これらが tactic の小技ではなく，Lean で標準的な数学を表現するための基礎的な仕組みだという点です．
一方で，証明項を構成しているという基本的な見方は変わりません．
古典論理や選択を使う場合も，Lean はその原理を使った証明項を構成し，カーネルが型を確認しています．

---
## `induction`: 帰納法

自然数やリストのような帰納型について証明するときは，`induction` を使います．
自然数 `n : Nat` に対する帰納法では，`zero` の場合と `succ n` の場合を証明します．
`cases` が単なる場合分けであるのに対して，`induction` は再帰的なコンストラクタの枝で帰納法の仮定を生成します．

```lean
theorem nat_add_assoc_by_induction (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      simp [Nat.succ_add, ih]
```

帰納法の帰納ステップでは，`ih` が帰納法の仮定です．
上の例では，`ih : (a + b) + c = a + (b + c)` を使って，`Nat.succ a` の場合を示しています．

```lean
theorem list_length_map_by_induction {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]
```

自分で定義した帰納型に対しても `cases` や `induction` を使えます．
次の `Even` は「偶数である」という命題を帰納的に定義したものです．
`Even n` は `n` が偶数であることを表す命題であり，その証明は `zero` と `add_two` から作られます．

```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two {n : Nat} : Even n → Even (n + 2)

example : Even 4 := by
  apply Even.add_two
  apply Even.add_two
  exact Even.zero

example (h : Even 1) : False := by
  cases h
```

帰納的に定義された命題の証明 `h : Even n` に対しても `induction h` が使えます．
これは「その証明がどのコンストラクタで作られたか」に関する帰納法です．
`cases h` は不可能なコンストラクタの枝を自動的に消すため，`Even 1` からは矛盾が得られます．

```lean
theorem even_plus_two_of_even {n : Nat} (h : Even n) : Even (n + 2) := by
  exact Even.add_two h

example (n : Nat) (h : Even n) : Even (n + 2) := by
  induction h with
  | zero =>
      exact Even.add_two Even.zero
  | add_two h ih =>
      exact Even.add_two ih
```

---
## 汎用的な tactic

### `decide`
Lean が真偽を計算できる命題を決定して証明します．
有限な計算で判定できる命題に有効です．
対象の命題に対する `Decidable` インスタンスがあり，計算結果が真である場合にゴールを閉じます．

```lean
example : 3 < 5 := by
  decide

example : (2 + 2 = 4) := by
  decide
```

### `grind`
書き換え，前向き推論，後ろ向き推論，場合分けなどを組み合わせる汎用自動化 tactic です．
強力ですが，何をしたのかが見えにくくなることもあるので，講義資料では短い例に限定して使います．
自動化 tactic は証明を短くしますが，初学段階ではまず手動の tactic でゴールの変化を追えるようにしておくことが重要です．

```lean
example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  grind

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  grind
```

`simp` や `grind` は便利ですが，証明が通らないときに原因を理解しにくいことがあります．
最初は `intro`，`apply`，`constructor`，`cases`，`rw` などで証明構造を書けるようにしてから，自動化を使うのがよいです．

---
## 検索系: `#check`，`exact?`，`rw?`

使える補題を探すことは，Lean で数学を形式化するときの大きな作業です．

### `#check`
名前が分かっている定理の型を確認します．
定理名が分かっている場合は `#check`，現在のゴールから候補を探したい場合は `exact?`，`rw?` のような検索支援を使い分けます．

```lean
#check Nat.add_comm
#check Nat.add_assoc
```

### `exact?`，`rw?`，`try?`
現在のゴールを閉じる候補や書き換え候補を提案する tactic です．
出力は Lean のバージョンや読み込んだライブラリによって変わることがあるため，この資料では実行例としてだけ示します．

```lean
example (n : Nat) : n + 0 = n := by
  exact?

example (a b : Nat) : a + b = b + a := by
  rw?

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  try?
```

Mathlib には `#loogle` などのより強力な検索支援もあります．
それらは次章以降，Mathlib を使う場面で扱います．

---
## まとめ

tactic モードでは，現在のゴールとローカルコンテキストを見ながら，証明を小さなステップに分解します．
`rw` と `simp` は書き換え，`intro` と `apply` は含意や全称命題，`constructor` と `cases` は論理結合子や帰納型，`induction` は帰納法に対応します．

`calc` は，数学の計算に近い形で等式や不等式の連鎖を書くための構文です．
`grind` は強力な自動化ですが，まずは基本 tactic で証明の構造を理解することが重要です．

---
## 演習問題

この章の演習では，同じ命題を複数の書き方で証明することを重視します．
まず tactic mode で証明し，余裕があれば term mode や `calc` でも書き直してください．

1. `intro` と `exact` だけで証明してください．

    ```lean4
    example (P Q : Prop) (hQ : Q) : P → Q := by
      sorry
    ```

2. `constructor` と `cases` を使って，連言の順序を入れ替えてください．

    ```lean4
    example (P Q : Prop) : P ∧ Q → Q ∧ P := by
      sorry
    ```

3. `rw` を使って等式を書き換えてください．

    ```lean4
    example (a b c : Nat) (h : a = b) : a + c = b + c := by
      sorry
    ```

4. `calc` モードで加法の結合律・可換律を使って証明してください．

    ```lean4
    example (a b c : Nat) : a + b + c = b + a + c := by
      calc
        a + b + c = b + a + c := by
          -- `ac_rfl` または `rw [Nat.add_comm a b]` などを試す．
          sorry
    ```

5. `induction` で自然数の加法単位元を証明してください．

    ```lean4
    example (n : Nat) : n + 0 = n := by
      induction n with
      | zero =>
          sorry
      | succ n ih =>
          sorry
    ```

6. `conv` を使って，ゴールの一部だけを書き換えてください．

    ```lean4
    example (a b c : Nat) : (a + b) + c = (b + a) + c := by
      -- ヒント:
      --   conv =>
      --     lhs
      --     rw [Nat.add_comm a b]
      sorry
    ```

7. `simp` で証明できる命題を，まず手動で証明し，その後 `simp` で短くしてください．

    ```lean4
    example (n : Nat) : n + 0 = n := by
      -- まず `induction`，次に `simpa` で試す．
      sorry
    ```

8. `grind` で閉じる論理問題を作り，手動証明と比較してください．

    ```lean4
    example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (hP : P) : R := by
      -- `grind`
      sorry
    ```

9. `funext` を使って，点ごとの等式から関数の等式を証明してください．

    ```lean4
    example (f g : Nat → Nat) (h : ∀ n : Nat, f n = g n) : f = g := by
      sorry
    ```

10. `propext` を使って，論理的に同値な命題を等しい命題として扱ってください．

    ```lean4
    example (P Q : Prop) (h : P ↔ Q) : P = Q := by
      sorry
    ```

11. `Classical.choose` と `Classical.choose_spec` を使って，存在命題から証拠を取り出してください．

    ```lean4
    noncomputable def chosenNatExercise03 (h : ∃ n : Nat, n > 10) : Nat :=
      Classical.choose h

    example (h : ∃ n : Nat, n > 10) : chosenNatExercise03 h > 10 := by
      -- `Classical.choose_spec h`
      sorry
    ```

12. `Quot.sound` を使って，商型の中で代表元が等しいことを証明してください．

    ```lean4
    def sameModTwoExercise03 (a b : Nat) : Prop :=
      a % 2 = b % 2

    example : Quot.mk sameModTwoExercise03 1 = Quot.mk sameModTwoExercise03 3 := by
      -- `Quot.sound` と `decide`
      sorry
    ```
