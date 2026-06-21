# Chapter 01: 代数

Mathlib における代数構造の扱いを概観します．

参考:

* Mathematics in Lean, 9. Groups and Rings: <https://leanprover-community.github.io/mathematics_in_lean/C09_Groups_and_Rings.html>

中心になる考え方は次の 3 つです．

* 代数構造は型クラスで表す．
* 準同型や部分構造は bundled structure として表す．
* 具体的な計算には `simp`，`group`，`abel`，`ring` などの tactic を使う．

```lean
import Mathlib

namespace PracticeChapter01
```

---
## 代数構造は型クラスで表す

`Monoid M`，`Group G`，`Ring R`，`Field K` などは型 `M`，`G`，`R`，`K` に入っている構造を表す型クラスです．
数学では「群 G」と言うことが多いですが，Lean では「型 `G` と，その上の群構造 `[Group G]`」を分けて書きます．

```lean
#check Monoid
#check CommMonoid
#check Group
#check AddCommGroup
#check Semiring
#check Ring
#check CommRing
#check Field

section BasicStructures

variable {M : Type*} [Monoid M]

example (x : M) : x * 1 = x := by
  simp

example (x y z : M) : (x * y) * z = x * (y * z) := by
  exact mul_assoc x y z

variable {A : Type*} [AddCommMonoid A]

example (x y : A) : x + y = y + x := by
  exact add_comm x y

end BasicStructures
```

`Monoid` は乗法的な記法を使います．
加法的に書きたい場合は `AddMonoid` や `AddCommGroup` を使います．

同じ数学的事実でも，乗法的な構造では `mul_assoc`，加法的な構造では `add_assoc` のように名前が分かれます．

```lean
section Groups

variable {G H : Type*} [Group G] [Group H]

example (x : G) : x * x⁻¹ = 1 := by
  simp

example (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example (f : G →* H) (x : G) : f (x⁻¹) = (f x)⁻¹ := by
  exact map_inv f x

end Groups

section AdditiveGroups

variable {A : Type*} [AddCommGroup A]

example (x y z : A) : z + x + (y - z - x) = y := by
  abel

end AdditiveGroups
```

`group` は群の公理から従う等式を解く tactic です．
加法可換群では `abel` が使えます．
どちらも「代数構造の公理に従う正規化」を行うものだと考えるとよいです．

---
## 準同型

群準同型や環準同型は，単なる関数ではなく，関数と保存性の証明をまとめた構造体です．
このような表現を bundled map と呼びます．

モノイド準同型は `M →* N`，加法モノイド準同型は `M →+ N`，環準同型は `R →+* S` と書きます．

```lean
#check MonoidHom
#check AddMonoidHom
#check RingHom

section Homomorphisms

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

example (f : M →* N) (x y : M) : f (x * y) = f x * f y := by
  exact f.map_mul x y

example (f : M →* N) : f 1 = 1 := by
  exact f.map_one

example (f : M →* N) (g : N →* P) : M →* P :=
  g.comp f

variable {R S : Type*} [Ring R] [Ring S]

example (f : R →+* S) (x y : R) : f (x + y) = f x + f y := by
  exact map_add f x y

example (f : R →+* S) (x y : R) : f (x * y) = f x * f y := by
  exact map_mul f x y

example (f : R →+* S) : f 0 = 0 := by
  exact map_zero f

end Homomorphisms
```

準同型 `f : R →+* S` は関数として使えます．
一方で，普通の関数合成 `g ∘ f` ではなく，構造を保った合成には `comp` を使います．
これは，合成後の写像が演算を保存することも一緒に記録する必要があるためです．

---
## 部分群

`Subgroup G` は `G` の部分群の型です．
これは `Set G` に「閉性の証明」を追加した bundled structure です．
そのため，`x ∈ H` のように集合として使えますが，同時に部分群としての構造も持っています．

```lean
#check Subgroup
#check AddSubgroup

section Subgroups

variable {G H : Type*} [Group G] [Group H]
variable (S T : Subgroup G)

example {x y : G} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
  exact S.mul_mem hx hy

example {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  exact S.inv_mem hx

example : ((S ⊓ T : Subgroup G) : Set G) = (S : Set G) ∩ (T : Set G) := by
  rfl

example (x : G) : x ∈ (⊤ : Subgroup G) := by
  trivial

example (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := by
  exact Subgroup.mem_bot

variable (f : G →* H) (U : Subgroup H)

example : Subgroup H :=
  Subgroup.map f S

example : Subgroup G :=
  Subgroup.comap f U

example (x : G) : x ∈ Subgroup.comap f U ↔ f x ∈ U := by
  rfl

#check Subgroup.mem_map
#check MonoidHom.ker
#check MonoidHom.range

end Subgroups
```

部分群全体は包含関係で順序づけられ，束構造を持ちます．
`S ⊓ T` は交わりに対応します．
一方，`S ⊔ T` は単純な和集合ではなく，和集合で生成される部分群です．
これは「和集合は一般には部分群でない」ことを反映しています．

---
## 環とイデアル

環論でも同じ設計が現れます．
`Subring R` は部分環，`Ideal R` はイデアルを表す bundled structure です．
可換環のイデアルでは，加法で閉じていて，外からの積で閉じていることを使います．

```lean
#check Subring
#check Ideal
#check RingEquiv

section Ideals

variable {R : Type*} [CommRing R]
variable (I J : Ideal R)

example {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  exact I.add_mem hx hy

example {x : R} (hx : x ∈ I) (r : R) : r * x ∈ I := by
  exact I.mul_mem_left r hx

example : ((I ⊓ J : Ideal R) : Set R) = (I : Set R) ∩ (J : Set R) := by
  rfl

example (x : R) : x ∈ (⊥ : Ideal R) ↔ x = 0 := by
  exact Ideal.mem_bot

#check Ideal.Quotient.mk
#check Ideal.Quotient.eq_zero_iff_mem
#check Ideal.map
#check Ideal.comap

end Ideals
```

`Ideal.Quotient I` は商環です．
商を扱うときは，代表元に依存しない定義であることを証明する必要があります．
このため，最初は `#check` で定義や補題の型を確認しながら進めるのが安全です．

---
## 多項式と代数

Mathlib の多項式は `Polynomial R` です．
係数を埋め込む写像は `Polynomial.C`，不定元は `Polynomial.X` です．

```lean
#check Polynomial
#check Polynomial.C
#check Polynomial.X

section Polynomials

open Polynomial

variable {R : Type*} [Semiring R]

example : (X : Polynomial R) * C (1 : R) = X := by
  simp

example (a : R) : (C a : Polynomial R) + 0 = C a := by
  simp

end Polynomials
```

`Algebra R A` は，`A` が `R` 上の代数であることを表す型クラスです．
スカラー倍 `r • a` は，構造写像 `algebraMap R A r` による積として振る舞います．

```lean
#check Algebra
#check algebraMap

section Algebras

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

example (r : R) (a : A) : r • a = algebraMap R A r * a := by
  exact Algebra.smul_def r a

example (r s : R) : algebraMap R A (r + s) = algebraMap R A r + algebraMap R A s := by
  exact map_add (algebraMap R A) r s

end Algebras
```

---
## 長めの例: `ℤ` を `ℚ` の加法部分群として作る

紙の数学では「整数全体は有理数の加法部分群である」と簡単に書きます．
Lean では，これを `AddSubgroup ℚ` の項として作ります．

ポイントは次の通りです．

* 台集合は `Set.range ((↑) : ℤ → ℚ)` として表す．
* `0` が入ることを示す．
* 加法で閉じていることを示す．
* 負元で閉じていることを示す．

この例は，部分構造が「集合 + 閉性の証明」であることを具体的に示しています．

```lean
def integersInRationals : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  zero_mem' := by
    use 0
    norm_num
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    use m + n
    norm_num
  neg_mem' := by
    rintro _ ⟨m, rfl⟩
    use -m
    norm_num

example : (3 : ℚ) ∈ integersInRationals := by
  use (3 : ℤ)
  norm_num

example : (1 / 2 : ℚ) ∉ integersInRationals := by
  rintro ⟨z, hz⟩
  have htwo : ((2 * z : ℤ) : ℚ) = 1 := by
    norm_num [Int.cast_mul, hz]
  have hInt : (2 * z : ℤ) = 1 := by
    exact_mod_cast htwo
  omega
```

最後の例は少し人工的ですが，「`Set.range` の元である」という仮定を
`∃ z : ℤ, ...` として取り出し，整数性の情報を使って矛盾を出しています．

代数の形式化では，このように「集合としての記述」と「構造としての記述」を行き来することがよくあります．

---
## 長めの例: 共役部分群

群 `G` の部分群 `S` と元 `g : G` に対して，
`g S g⁻¹ = {x | ∃ s ∈ S, x = g * s * g⁻¹}` はまた部分群です．
これは抽象代数学の基本例で，閉性の証明に `group` がよく効きます．

```lean
section ConjugateSubgroup

variable {G : Type*} [Group G]

def conjugateSubgroup (g : G) (S : Subgroup G) : Subgroup G where
  carrier := {x : G | ∃ s, s ∈ S ∧ x = g * s * g⁻¹}
  one_mem' := by
    refine ⟨1, S.one_mem, ?_⟩
    group
  mul_mem' := by
    rintro x y ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    group
  inv_mem' := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, ?_⟩
    group

example (g : G) (S : Subgroup G) {x : G} :
    x ∈ conjugateSubgroup g S ↔ ∃ s, s ∈ S ∧ x = g * s * g⁻¹ := by
  rfl

example (S : Subgroup G) {x : G} : x ∈ conjugateSubgroup (1 : G) S ↔ x ∈ S := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro hx
    refine ⟨x, hx, ?_⟩
    group

end ConjugateSubgroup
```

この例で使った証明パターンは，部分構造の自作で頻繁に現れます．

* `rintro ... ⟨s, hs, rfl⟩` で存在記号と等式を分解する．
* 閉性は `S.mul_mem`，`S.inv_mem` などを使う．
* 群の計算は `group` に任せる．

学部レベルの代数を形式化するときは，まずこのような「集合を carrier として持つ構造体」を自作できることが重要です．

---
## まとめ

代数の章で重要なのは，「構造」と「その構造を保つ写像」を型として読むことです．
`Group G`，`Ring R`，`Module R M` のような型クラスが演算や公理を供給し，
`G →* H`，`R →+* S`，`Subgroup G`，`Ideal R` のような bundled structure が数学的対象を表します．

証明では，手で公理を展開する前に，`simp`，`group`，`abel`，`ring`，`rw`，`ext`，`#check` を使って既存の構造を利用します．

### 形式化の tips

代数の形式化では，次の順に考えると進めやすくなります．

1. 対象は型か，部分構造か，準同型かを決める．
2. 演算が使えないときは，必要な型クラス仮定を探す．
3. 部分構造の等式は `ext x` で元ごとの同値にする．
4. membership は `simp`，`rfl`，`Subgroup.mem_map` などで開く．
5. 群や環の計算は `group`，`abel`，`ring` に任せる．

---
## 演習問題

以下の問題は，講義中または自習で `by` 以下を埋めることを想定しています．
まずは `#check` で使えそうな補題を探し，`simp`，`group`，`abel`，`ring`，`ext` を試してください．

1. モノイド準同型の合成が積を保つことを示してください．

    ```lean4
    example {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
        (f : M →* N) (g : N →* P) (x y : M) :
        (g.comp f) (x * y) = (g.comp f) x * (g.comp f) y := by
      -- `map_mul` または `simp` を使う．
      sorry
    ```

2. 部分群の `map` が包含を保つことを示してください．

    ```lean4
    example {G H : Type*} [Group G] [Group H]
        (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) :
        Subgroup.map φ S ≤ Subgroup.map φ T := by
      -- `Subgroup.mem_map` で元を存在記号に分解する．
      sorry
    ```

3. 部分群の `comap` が包含を保つことを示してください．

    ```lean4
    example {G H : Type*} [Group G] [Group H]
        (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) :
        Subgroup.comap φ S ≤ Subgroup.comap φ T := by
      -- `rfl` で membership を展開できる．
      sorry
    ```

4. `conjugateSubgroup` について，`g⁻¹` で再び共役すると元に戻ることを示してください．

    ```lean4
    example {G : Type*} [Group G] (g : G) (S : Subgroup G) :
        conjugateSubgroup g⁻¹ (conjugateSubgroup g S) = S := by
      -- `ext x` で部分群の等式を元ごとの同値にする．
      -- その後，存在記号を分解して `group` を使う．
      sorry
    ```

5. 可換環のイデアル `I J : Ideal R` について，`I ⊓ J` の元であることを集合の交わりとして読み替えてください．

    ```lean4
    example {R : Type*} [CommRing R] (I J : Ideal R) (x : R) :
        x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := by
      -- `rfl` または `simp` を試す．
      sorry
    ```

6. 多項式で，定数多項式の和が係数の和に対応することを示してください．

    ```lean4
    example {R : Type*} [Semiring R] (a b : R) :
        (Polynomial.C a + Polynomial.C b : Polynomial R) = Polynomial.C (a + b) := by
      -- `ext n` または `simp` を試す．
      sorry
    ```

7. `MonoidHom.ker f` の membership を読み替えてください．

    ```lean4
    example {G H : Type*} [Group G] [Group H] (f : G →* H) (x : G) :
        x ∈ MonoidHom.ker f ↔ f x = 1 := by
      -- `f.mem_ker` を調べる．
      sorry
    ```

8. `MonoidHom.range f` の membership を読み替えてください．

    ```lean4
    example {G H : Type*} [Group G] [Group H] (f : G →* H) (y : H) :
        y ∈ MonoidHom.range f ↔ ∃ x : G, f x = y := by
      -- `f.mem_range` を調べる．
      sorry
    ```

9. 部分群の積で閉じていることを，`S.mul_mem` ではなく `show` でゴールを明示して証明してください．

    ```lean4
    example {G : Type*} [Group G] (S : Subgroup G) {x y : G}
        (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
      -- ヒント:
      --   show x * y ∈ S
      --   exact S.mul_mem hx hy
      sorry
    ```

10. 可換環で，イデアルの元に外から掛けてもイデアルに入ることを左右両方で確認してください．

    ```lean4
    example {R : Type*} [CommRing R] (I : Ideal R) {x : R} (hx : x ∈ I) (r : R) :
        x * r ∈ I := by
      -- 可換性で `r * x` に直すか，既存補題を探す．
      sorry
    ```
