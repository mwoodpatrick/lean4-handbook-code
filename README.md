# Lean 4 数学ハンドブック / Lean 4 Mathematics Handbook — コード / Code

このリポジトリには、日本語版と英語版の両方のコードが入っています。
This repository holds the code for both the Japanese and the English edition.

| | 書籍 / Book | ディレクトリ / Directory |
|---|---|---|
| 日本語 | 『Lean 4 数学ハンドブック — 高校数学から現代数学まで』 | `Handbook/` |
| English | *Lean 4 Mathematics Handbook — From High-School Mathematics to Modern Mathematics* | `Handbook_EN/` |

[日本語](#日本語) ・ [English](#english)

---

## 日本語

書籍『Lean 4 数学ハンドブック — 高校数学から現代数学まで』に掲載した
Lean 4 コードの完全版です。

本書のコード枠は、すべてこのリポジトリの実ファイルから機械的に切り出して
います。本文用に書き直したコードは存在しません。したがって、本に載っている
コードはここでそのまま動きます。

### 動かす

```bash
lake exe cache get   # ビルド済み mathlib を取得(これを飛ばすと数時間かかる)
lake build           # 全コードを検証(日本語版・英語版の両方)
```

`lean-toolchain` に書かれた版を elan が自動で導入するので、Lean の
バージョンを手で指定する必要はありません。

日本語版だけを検証したいときは `lake build Handbook`、
英語版だけなら `lake build Handbook_EN` を使ってください。

### 検証環境

| | |
|---|---|
| Lean | v4.32.0 |
| mathlib | v4.32.0 |

版を固定しています。mathlib は活発に開発されており、版が違えば宣言名が
変わっていることがあります。本書のコードが手元で通らないときは、まず
`lean-toolchain` を照合してください。

日本語版・英語版とも全 218 ファイルが `lake build` を通過しています。
`sorry` は使っていません。

### 構成

章ごとのディレクトリの下に、節ごとのファイルが並びます。

```
Handbook/              日本語版
├── C02_Tour/          第2章 Lean 4 ツアー
├── C03_Setup/         第3章 環境構築
├── C04_Language/      第4章 Lean 言語の基礎
├── C05_Proofs/        第5章 証明の基本
├── C06_Numbers/ …     第6章以降(第II部 高校数学)
├── C16_Sets/ …        第16章以降(第III部 大学教養)
├── C28_Foundations/ … 第28章以降(第IV部 現代数学)
├── C40_Mathlib/ …     第40章以降(第V部 Lean の深層)
└── AppA_Tactics/      付録A tactic リファレンス

Handbook_EN/           英語版(同じ章立て、コメントは英語)
```

第1章(読み方)と第43章(プロジェクトの設計)にはコードがないため、
対応するディレクトリはありません。

`Handbook/` と `Handbook_EN/` はファイル単位で対応しています(同じパスに
同じ名前のファイルが 218 ずつ)。ただし英語版は逐語訳ではありません。
コメントの言語が違うほか、53 ファイルはコードそのものも異なります
(取り上げる例を差し替えたもの、英語版で証明を書き直したものがあります)。

### 本文との対応

各ファイルには `-- BOOK: begin <タグ>` と `-- BOOK: end <タグ>` の
マーカーが入っています。本に載っているのはこの区間です。マーカーの外にも
検証済みのコードがあり、本では紙幅の都合で省いています。

### 正誤表

[ERRATA.md](ERRATA.md) に置いています。誤りを見つけたら Issue で
知らせてください。

### ライセンス

このリポジトリのコードは MIT ライセンスです([LICENSE](LICENSE))。
書籍の本文・図版の著作権は著者に帰属します。

---

## English

The complete Lean 4 code printed in *Lean 4 Mathematics Handbook — From
High-School Mathematics to Modern Mathematics*.

Every code box in the book is extracted mechanically from the real files in
this repository. No code was rewritten for the page, so what is printed in the
book runs here as it stands.

### Running it

```bash
lake exe cache get   # fetch the prebuilt mathlib (skipping this costs hours)
lake build           # check all the code, both editions
```

`elan` installs the release recorded in `lean-toolchain` on its own, so there
is no need to name a Lean version by hand.

To check one edition only, use `lake build Handbook_EN` for the English
sources or `lake build Handbook` for the Japanese ones.

### Verified environment

| | |
|---|---|
| Lean | v4.32.0 |
| mathlib | v4.32.0 |

The versions are pinned. mathlib is developed actively and declaration names
change between releases, so if the book's code does not go through on your
machine, check `lean-toolchain` first.

All 218 files pass `lake build` in each edition. No `sorry` is used
anywhere.

### Layout

Under `Handbook_EN/` there is one directory per chapter and one file per
section.

```
Handbook_EN/           English edition
├── C02_Tour/          Chapter 2  A tour of Lean 4
├── C03_Setup/         Chapter 3  Setting up
├── C04_Language/      Chapter 4  The Lean language
├── C05_Proofs/        Chapter 5  Writing proofs
├── C06_Numbers/ …     Chapter 6 on (Part II, school mathematics)
├── C16_Sets/ …        Chapter 16 on (Part III, analysis and linear algebra)
├── C28_Foundations/ … Chapter 28 on (Part IV, modern mathematics)
├── C40_Mathlib/ …     Chapter 40 on (Part V, mastering Lean)
└── AppA_Tactics/      Appendix A, the tactic reference

Handbook/              Japanese edition (same chapter plan, Japanese comments)
```

Chapter 1 (how to read the book) and Chapter 43 (designing a project) carry no
code, so they have no directory.

`Handbook/` and `Handbook_EN/` correspond file for file: 218 files each, at
the same paths under the same names. The English edition is not a word-for-word
translation, though. Besides the language of the comments, 53 files differ in
the code itself, where a worked example was replaced or a proof rewritten for
the English edition.

### How the code maps to the book

Each file carries `-- BOOK: begin <tag>` and `-- BOOK: end <tag>` markers. What
is printed in the book is exactly the region between them. There is verified
code outside the markers too, left out of the book for want of space.

### Errata

Kept in [ERRATA.md](ERRATA.md). If you find a mistake, please open an issue.

### License

The code in this repository is MIT licensed ([LICENSE](LICENSE)). The text and
figures of the books themselves are not.
