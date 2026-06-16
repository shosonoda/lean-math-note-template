# Lean 4 + Mathlib Course Template

Lean 4 と [Mathlib](https://github.com/leanprover-community/mathlib4) を、GitHub Codespaces 上ですぐに使えるプロジェクトテンプレートです。

ローカル環境に Lean や VS Code 拡張をインストールする必要はありません。ブラウザ上で Codespace を起動すると、Lean 4 + Mathlib の環境が自動で用意されます。

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/yuta0x89/lean-course-template?quickstart=1)

## 使い方

### 1. Codespace を起動する

上の **Open in GitHub Codespaces** ボタンを押してください。

または、GitHub の画面から次の手順で起動できます。

1. **Code** ボタンを押す
2. **Codespaces** タブを開く
3. **Create codespace on main** を押す

初回起動時には、Lean / Mathlib の準備のために数分かかることがあります。

### 2. Lean ファイルを開く

Codespace が起動したら、次のファイルを開いてください。

[LeanTemplate/Basic.lean](LeanTemplate/Basic.lean)

このファイルを編集して、定義や証明を書いていきます。

### 3. 動作確認

`LeanTemplate/Basic.lean` には、次のような簡単な例が含まれています。

```lean
import Mathlib

example (n : ℕ) : n + 0 = n := by
  simp
```

エディタ上でエラーが表示されなければ、Lean と Mathlib の環境は正しく動作しています。

## 講義後の注意

Codespace は起動している間、GitHub Codespaces の利用時間を消費します。講義が終わったら、不要な Codespace は停止または削除してください。

GitHub の左下メニュー、または GitHub の Codespaces 管理画面から停止・削除できます。

## バージョン

* Lean 4.28.0
* Mathlib は `lakefile.toml` で指定されたバージョンを使用します。
