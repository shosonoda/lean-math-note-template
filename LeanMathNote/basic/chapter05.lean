--#--
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
--#--
/-
# Chapter 05: Lean Project の作成と操作

この章では，Lean project を新しく作る方法，既存 project を開く方法，Lean のバージョンを指定する方法，
Mathlib を依存関係として追加する方法，Lake の基本操作を説明します．

Lean のファイルは，単独の `.lean` ファイルとして扱うより，基本的には project の中で扱います．
project は，`lean-toolchain`，`lakefile.toml` または `lakefile.lean`，`lake-manifest.json`，
ソースディレクトリ，`.lake/` 以下の依存関係とビルド成果物をまとめて管理する単位です．

参考:

* Lean Community, Lean projects: <https://leanprover-community.github.io/install/project.html>
* Lean のインストール方法・elan と Lake の使い方，Lean プロジェクトの作り方: <https://aconite-ac.github.io/how_to_install_lean/lake-package-manager/how-to-create-project.html>

!!! Caution "Mathlib を含む Lean project は容量をかなり使います．"
    Mathlib の依存パッケージ，ビルド済みキャッシュ，`.lake/` 以下の成果物を含めると，少なくとも 7.2 GB 程度の空き容量を見込んでください（2026年6月時点の実績）．
    空き容量が少ない状態で `lake update` や `lake exe cache get` を実行すると，途中で失敗したり，壊れたキャッシュが残ったりします．
-/
import Mathlib
set_option linter.missingDocs false --#

namespace Chapter05

/-
---
## Elan, Lean, Lake

Lean project を扱うときに出てくる主な道具は次の 3 つです．

| 名前 | 役割 |
| --- | --- |
| `elan` | Lean toolchain manager．どの Lean バージョンを使うかを選ぶ． |
| `lean` | Lean 本体．`.lean` ファイルを読み，型検査や elaboration を行う． |
| `lake` | Lean の package manager / build tool．project 作成，依存関係，ビルドを管理する． |

通常，ユーザーが直接呼び出す `lean` や `lake` は Elan の proxy です．
カレントディレクトリか親ディレクトリに `lean-toolchain` があれば，Elan はそこに書かれた toolchain を使います．

たとえばこの project の `lean-toolchain` は次のような 1 行のファイルです．

```text
leanprover/lean4:v4.30.0
```

この指定により，この project では Lean 4.30.0 系の `lean` と `lake` が使われます．
-/

/-
---
## Lean バージョンの指定法

Lean のバージョン指定は，project ルートの `lean-toolchain` に書くのが基本です．

```text
leanprover/lean4:v4.30.0
```

このファイルを commit しておくと，別の計算機で project を開いたときにも同じ Lean バージョンが使われます．
講義資料，論文付録，研究プロジェクトでは，Lean と Mathlib のバージョンを固定することが再現性のために重要です．

一時的に特定バージョンのコマンドを使いたい場合は，Elan の `+toolchain` 記法を使えます．

```bash
lake +v4.30.0 --version
lean +v4.30.0 --version
```

ただし，project の通常運用では `lean-toolchain` を編集して管理する方が分かりやすいです．
`lake +v4.30.0 new my_project math` のように書いた場合，そのコマンドを実行する `lake` のバージョンを指定しているのであって，
作られる project の Lean バージョンを恒久的に指定する主な方法は，作成後の `lean-toolchain` です．

現在使われている toolchain を確認するには次を使います．

```bash
elan show
lean --version
lake --version
cat lean-toolchain
```
-/

/-
---
## Mathlib を含まない project を作る

Mathlib を使わない最小 project は次で作れます．

```bash
lake new my_project
cd my_project
lake build
```

`lake new my_project` は，現在のディレクトリの下に `my_project/` を作り，その中に Lake package を生成します．
生成される典型的な構成は次のようなものです．

```text
my_project/
  lakefile.toml
  lean-toolchain
  MyProject.lean
  MyProject/
    Basic.lean
```

Lean の module 名はファイルパスに対応します．
たとえば `MyProject/Basic.lean` は，通常 `import MyProject.Basic` で import できます．

`lake init my_project` という作り方もあります．
これは，すでに存在する空ディレクトリの中で project を初期化したいときに使います．

```bash
mkdir my_project
cd my_project
lake init my_project
```
-/

/-
---
## Mathlib を含む project を作る

数学の形式化では，ほとんどの場合 Mathlib を使います．
Mathlib 付きの project は次で作ります．

```bash
lake new my_project math
cd my_project
lake update
lake exe cache get
```

`math` は，Mathlib を依存関係に含める template です．
これにより，project 内の Lean ファイルで

```lean4
import Mathlib
```

または

```lean4
import Mathlib.Topology.Basic
```

のように書けるようになります．

`lake update` は依存関係を解決し，`lake-manifest.json` を更新します．
`lake exe cache get` は Mathlib のビルド済みキャッシュを取得します．
Mathlib 全体を手元で最初からビルドすると時間がかかるため，通常はキャッシュを取得してから作業します．

注意: Mathlib を含む project では，`.lake/` と Mathlib cache に大きな容量が必要です．
少なくとも 7.2 GB 程度の空き容量を確保してから作成してください．
-/

/-
---
## 既存 project に Mathlib を追加する

すでにある Lean project に Mathlib を追加するには，Lean バージョンと Mathlib のバージョンを揃える必要があります．
Mathlib は Lean 本体の特定バージョンに依存しているため，適当な Lean バージョンと適当な Mathlib revision を混ぜると，
`lake update` や `import Mathlib` でエラーになります．

この資料のように `lakefile.toml` を使う場合，たとえば Lean 4.30.0 に対応する Mathlib release を使うなら，
`lean-toolchain` を次のようにします．

```text
leanprover/lean4:v4.30.0
```

そして `lakefile.toml` に Mathlib の依存関係を追加します．

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0"
```

追加後，project ルートで次を実行します．

```bash
lake update
lake exe cache get
lake build
```

`lakefile.lean` を使う project なら，依存関係は次のように書きます．

```lean4
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
```

Mathlib の最新版 `master` に追随する場合は，Mathlib 側の `lean-toolchain` に Lean バージョンを合わせます．

```bash
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get
```

ただし，講義資料や共同研究では，毎回 `master` に追随するより，特定の release tag や commit hash に固定する方が安定です．
-/

/-
---
## 既存 project を開く

GitHub などから既存 project を取得したら，まず project ルートに移動します．

```bash
git clone https://github.com/USER/PROJECT.git
cd PROJECT
```

Mathlib を使う project なら，通常は次を実行します．

```bash
lake update
lake exe cache get
lake build
```

`lake update` は `lake-manifest.json` を更新することがあるため，
単に既存 project を使うだけなら，まず `lake exe cache get` と `lake build` で足りることもあります．
共同開発中の project で `lake-manifest.json` を勝手に更新したくない場合は，実行前に差分が出てもよいか確認してください．

VS Code で開くときは，`LeanMathNote/` のようなソースディレクトリではなく，`lakefile.toml` と `lean-toolchain` がある project ルートを開きます．
-/

/-
---
## Lake の基本操作

よく使う Lake コマンドをまとめます．

```bash
lake build                 # project 全体をビルドする
lake build MyProject.Basic # 特定 module / target をビルドする
lake env lean Foo.lean     # project の依存関係を含む環境で Lean を起動する
lake update                # 依存関係を解決し lake-manifest.json を更新する
lake exe cache get         # Mathlib のビルド済みキャッシュを取得する
lake clean                 # この package の build outputs を削除する
```

`lake clean` は，ビルド成果物を消して作り直したいときに使います．
典型的には `.lake/build/` 以下の成果物が対象であり，Lean toolchain そのものや，
Mathlib の全キャッシュを完全に削除するためのコマンドではありません．
依存関係や cache まで含めて大きく掃除したい場合は，何を消すかを理解してから手動で行ってください．

容量を確認したいときは，たとえば次のようにします．

```bash
du -sh .lake
df -h .
```

macOS や Linux では，`.lake/` が project 内で大きくなりやすいディレクトリです．
不要になった実験 project は，project ディレクトリごと削除して構いません．
一方で，作業中の project の `.lake/` を消すと，依存関係やビルド成果物を再取得・再ビルドする必要があります．
-/

/-
---
## project の中で Lean ファイルを確認する

project の依存関係を使って 1 ファイルを確認したいときは，`lake env lean` を使います．

```bash
lake env lean MyProject/Basic.lean
```

`import Mathlib` を含むファイルを素の `lean MyProject/Basic.lean` で実行すると，
Mathlib が見つからないことがあります．
`lake env` は，Lake workspace の依存関係を含む環境変数を設定したうえでコマンドを実行します．

この project なら，たとえば次のように章単体を確認できます．

```bash
lake env lean LeanMathNote/basic/chapter05.lean
lake build LeanMathNote.basic.chapter05
```

前者はファイルパスで Lean を直接実行し，後者は Lake target として module をビルドします．
-/

/-
---
## よくある失敗

Lean project の操作でよくある失敗をまとめます．

* `lakefile.toml` がある directory ではなく，その下のソース directory を VS Code で開いている．
* `lean-toolchain` と Mathlib の revision が対応していない．
* `lake update` 後に `lake exe cache get` を実行しておらず，Mathlib を手元で長時間ビルドしている．
* 空き容量が足りない．Mathlib project では 7.2 GB 程度の余裕を見込む．
* `lake update` によって `lake-manifest.json` が変わったことに気づかず commit してしまう．
* `lake clean` を cache 削除コマンドだと思っている．これは主に build outputs を消すためのコマンドである．

困ったときは，まず次を確認します．

```bash
pwd
ls
cat lean-toolchain
lake --version
lake build
git status --short
```
-/

/-
---
## まとめ

Lean project は，Lean ファイルの置き場というだけでなく，Lean バージョン，依存関係，module，ビルド成果物をまとめて管理する単位です．

* Lean バージョンは `lean-toolchain` で固定する．
* Mathlib なしなら `lake new my_project` でよい．
* Mathlib ありなら `lake new my_project math` の後に `lake update` と `lake exe cache get` を実行する．
* 既存 project に Mathlib を追加するときは，`lean-toolchain` と Mathlib revision を対応させる．
* `lake build`，`lake env lean`，`lake clean` の役割を区別する．

この章の内容を押さえると，次章の Lean の内部構造や build artifact の説明を読みやすくなります．
-/

/-
---
## 演習問題

1. 空き容量を確認してください．Mathlib を含む project を作る前に，7.2 GB 程度の余裕があるか確認します．

    ```bash
    df -h .
    ```

2. Mathlib を含まない project を一時ディレクトリに作り，`lake build` してください．

    ```bash
    cd /tmp
    lake new lean_sandbox
    cd lean_sandbox
    lake build
    ```

3. Mathlib を含む project を作る手順を，実行せずに説明してください．

    ```bash
    lake new lean_math_sandbox math
    cd lean_math_sandbox
    lake update
    lake exe cache get
    ```

4. `lean-toolchain` を開き，どの Lean バージョンが指定されているか確認してください．

    ```bash
    cat lean-toolchain
    elan show
    ```

5. この project の `lakefile.toml` を読み，`[[lean_lib]]` と `[[require]]` が何を指定しているか説明してください．

6. `lake clean` を実行すると何が消えるか，実行前に説明してください．
   講義中に実行する場合は，`git status --short` と `du -sh .lake` を先に確認してください．
-/

--#--
#check Nat
--#--

end Chapter05 --#
