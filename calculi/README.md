# Propositional LK / NK over pa

`zfc/` と並ぶ独立した開発ディレクトリです。古典命題論理の自然演繹 NK と、
複数の結論を持つシーケント計算 LK を、固定 pa prelude と証明項で実装します。
**tp コンパイラは使いません。** OCaml で λΠ の AST を構築し、既存の pa writer で出力します。
親プロジェクトのカーネル・コンパイラや `zfc/` のファイルは変更しません。

対象は原子命題、⊥、⊤、含意、連言、選言、否定です。量化子・等号は対象外です。
原子命題の番号は `Index` の `zero` / `succ` で表します。

## 体系と表現

| pa の型 | 表す判断 |
| --- | --- |
| `InContext A G` | A が文脈 G に含まれるという証拠 |
| `Perm G H` | G と H が順序の違いだけで一致するという証拠 |
| `NK G A` | 仮定 G から A への自然演繹 |
| `LK G D` | シーケント G ⊢ D の導出 |

文脈は `nil` / `cons` によるリストです。NK の仮定解除は、
`NK (cons A G) B` から `NK G (Imp A B)` を作る規則などで明示します。
古典規則は `NK (cons (Neg A) G) Bottom` から `NK G A` を導きます。

LK は恒等、⊥左、⊤右、左右の弱化・縮約・交換、各結合子の左右規則、cut を持ちます。
交換には任意の位置の入れ替えを表せる `Perm` の証拠が必要です。
二前提規則は文脈を共有する形を採用しました。例えば cut は

```text
LK G (cons A D) -> LK (cons A G) D -> LK G D
```

です。通常の文脈を分割する規則との同値性は、弱化・縮約・交換を使って示せるものですが、
この開発でその同値性を Rocq に証明したわけではありません。

## ファイル

- `export.ml`: 固定の56宣言と、証明付きの6宣言を直接 AST から pa に出力。
  出力前に OCaml カーネルでも型を検査します。
- `Calculi.v`: pa に依存しない NK・LK の帰納的定義と意味論的健全性。
  任意の原子命題の解釈に対し、古典論理を明示的な引数として渡す定理です。
  新たな Rocq の `Axiom` や `Admitted` は使いません。
- `Encoding.v`: 独立した式・文脈から pa AST への符号化、往復変換と式の単射性。
- `Verification.v`: 実際に生成した AST の受理、固定署名の整形式性、証明の型付け、
  証明本体への公理追加禁止、および6つの出力定理の型と意図した命題との一致。
- `test.py`: OCaml と Rocq 抽出版の両方で、pa バイト列の受理・拒否を検査。

証明例は NK の `A → A`、連言の交換、排中律、および LK の `⊢ A → A`、排中律、
cut による `A ⊢ A` です。すべて命題を引数に取る一般的な証明項です。

## 実行

OCaml・Dune は親プロジェクトと共通です。形式証明には Rocq が必要です。

```sh
make -C calculi test ROCQ=/path/to/bin/rocq
```

この作業環境での検証コマンドは次のとおりです。

```sh
make -C calculi test ROCQ=/private/tmp/rocq4pa-toolchain/_opam/bin/rocq
```

pa の生成だけなら Rocq は不要です。

```sh
make -C calculi export
dune exec bin/main.exe -- check calculi/_build/proofs.pa --prelude calculi/_build/prelude.pa
rocq4pa/_build/rocq4pa check calculi/_build/proofs.pa --prelude calculi/_build/prelude.pa
```

生成物は `calculi/_build/` の `prelude.pa`、`proofs.pa`、`names.txt`、`Artifact.v` です。
`names.txt` の行番号から1を引くと定数番号になります。
証明本体に `:` はありません。`--prelude` により追加の公理を禁止します。

テストは6つの一般的な証明と4つの具体的な利用に加え、12種類の不正入力を拒否することを確認します。
対象には仮定の不正な除去、文脈所属の偽装、交換の偽装、cut の命題不一致、
NK と LK の証明の混用、公理混入、自由変数と sort の不一致を含みます。

## 証明した範囲と残る作業

命題論理の規則ライブラリと、pa 証明の検査経路は実装済みです。
独立した Rocq の NK・LK の意味論的健全性、および実際の生成証明の LF 型付けは証明済みです。
**両者を結ぶ、任意の導出の翻訳と任意の LF 証明項からの導出復元は未証明です。**
従って、NK/LK の証明可能性と pa の受理が同値であるという定理はまだ主張しません。
カット除去、NK/LK 間の翻訳、自動証明探索も未実装です。

pa の固定 prelude は検査器に渡す信頼する前提です。型検査の成功だけで、
各規則が意図した論理を正確に表すことの形式証明にはなりません。
`Artifact.v` は同じ AST の独立再検査に使いますが、pa のパーサー・writer と AST の
バイト列レベルの対応は形式検証していません。pa バイト列については両 CLI の実行テストを行います。
