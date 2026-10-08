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
  NK 専用・LK 専用の prelude と証明例も生成し、各シグネチャを独立した OCaml カーネルで検査します。
- `Calculi.v`: pa に依存しない NK・LK の帰納的定義と意味論的健全性。
  任意の原子命題の解釈に対し、古典論理を明示的な引数として渡す定理です。
  新たな Rocq の `Axiom` や `Admitted` は使いません。
- `Encoding.v`: 独立した式・文脈から pa AST への符号化、往復変換と式の単射性。
- `Verification.v`: 実際に生成した AST の受理、固定シグネチャの整形式性、証明の型付け、
  証明本体への公理追加禁止、および6つの出力定理の型と意図した命題との一致。
- `Derivations.v`: NK・LK の任意の導出について、符号化した判断の LF 証明項が
  固定シグネチャ上で存在することを証明。文脈所属、置換、全規則の型付けと、
  追加の仮定を含まない単一の pa 証明宣言の妥当性も証明します。
- `Restoration.v`: 固定シグネチャ上の任意の閉じた LF 証明項から NK・LK の導出を復元。
  強正規化・型保存を使い、β 簡約を含む証明項も扱います。導出の存在と LF 型付け、
  および十分な fuel を持つ AST 検査器の受理との同値性を証明します。
- `CutElimination.v`: cut 以外の同じ17規則を持つ `LK_cut_free` を定義し、
  真偽値意味論に対する完全性から LK のカット除去と cut の許容性を証明します。
- `Examples.v`: β 簡約を含む LF 証明の復元、複合命題に対する入れ子の cut の除去、
  カットなしの排中律・含意左規則、および空のシーケントを証明できないことの回帰例。
- `test.py`: OCaml と Rocq 抽出版の両方で、pa バイト列の受理・拒否を検査。

証明例は NK の `A → A`、連言の交換、排中律、および LK の `⊢ A → A`、排中律、
cut による `A ⊢ A` です。すべて命題を引数に取る一般的な証明項です。

## 実行

OCaml・Dune は親プロジェクトと共通です。形式証明には Rocq が必要です。

```sh
make -C calculi test ROCQ=/path/to/bin/rocq
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

NK・LK を個別に使う場合は、同じ `make -C calculi export` で生成される次のファイルを使います。

| 体系 | prelude | 証明例 | 定数名・番号 | 宣言数 |
| --- | --- | --- | --- | --- |
| NK | `nk-prelude.pa` | `nk-proofs.pa` | `nk-names.txt` | 32前提・3証明 |
| LK | `lk-prelude.pa` | `lk-proofs.pa` | `lk-names.txt` | 38前提・3証明 |

共通の式・文脈定義に、NK 版は文脈所属と NK の規則、LK 版は置換と LK の規則を加えます。
各版の定数番号は独立して振り直すため、対応する名前表・証明ファイルを組み合わせて使います。

```sh
dune exec bin/main.exe -- check calculi/_build/nk-proofs.pa --prelude calculi/_build/nk-prelude.pa
dune exec bin/main.exe -- check calculi/_build/lk-proofs.pa --prelude calculi/_build/lk-prelude.pa
```

`NKArtifact.v` / `LKArtifact.v` も生成し、`Verification.v` で各 prelude の整形式性と
各証明例の型付けを再検査します。後述の復元・同値性の定理は結合版の固定シグネチャが対象です。

テストは6つの一般的な証明と4つの具体的な利用に加え、12種類の不正入力を拒否することを確認します。
対象には仮定の不正な除去、文脈所属の偽装、交換の偽装、cut の命題不一致、
NK と LK の証明の混用、公理混入、自由変数とソートの不一致を含みます。
Rocq 側では `Examples.v` の回帰例もコンパイルし、全モジュールを `rocq check` で再検査します。
分離版についても、両 CLI で証明例と具体的な恒等判断を受理し、不正な結論と追加公理を拒否することを確認します。

## 証明した範囲と残る作業

命題論理の規則ライブラリと、pa 証明の検査経路は実装済みです。
独立した Rocq の NK・LK の意味論的健全性、および実際の生成証明の LF 型付けは証明済みです。
任意の NK・LK 導出から、符号化した判断の LF 証明項が存在する方向は、
`NK_has_lf_derivation` / `LK_has_lf_derivation` として証明済みです。
全規則の定数型を実際の固定シグネチャで照合し、LF の定数・適用規則から型付けを構成します。
`NK_has_valid_pa_proof` / `LK_has_valid_pa_proof` は、これらの証明項を追加の仮定なしに
pa の妥当な証明宣言として追加できることも示します。新たな公理には依存しません。

逆方向は `LF_restores_NK` / `LF_restores_LK` として証明済みです。
対象は、固定 prelude のみをシグネチャとし、空の LF 変数文脈で、符号化した判断に
型付けされる任意の証明項です。正規化前のラムダ抽象や β 簡約も許します。
型付けされた正規形を定数・適用の形に分類し、固定の56定数が表すデータ・規則を解釈して復元します。
任意の追加公理や、宣言本体を展開しない追加の定理定数を持つシグネチャまでは扱いません。

`NK_LF_adequacy` / `LK_LF_adequacy` は導出の存在と LF 証明項の存在の同値性を、
`NK_checker_adequacy` / `LK_checker_adequacy` は十分な fuel を持つ AST 検査器に
受理される証明項の存在との同値性を示します。全証明を固定の fuel 128 で受理できるという主張ではありません。

`LK_cut_elimination` は任意の LK 導出から `LK_cut_free` の導出を得ます。
`LK_cut_admissible` はカットなしの二前提からカットなしの結論を導きます。
真偽値の解釈と式の重みによる帰納法を使い、排中律の公理にも依存しません。
`LF_restores_cut_free_LK` は LF 証明項からカットなしの LK 導出が得られることも示します。

独立した導出は `Prop` に属するため、これらは導出・証明項の存在証明です。
実行可能な導出データ型、復元器、cut の局所的な書き換えを行う実行可能な変換器は提供していません。
NK/LK 間の翻訳と自動証明探索は、この開発の対象外です。

pa の固定 prelude は検査器に渡す前提であり、その実際の AST を使って上記の対応を証明しています。
`Artifact.v` は同じ AST の独立再検査に使いますが、pa のパーサー・writer と AST の
バイト列レベルの対応は形式検証していません。pa バイト列については両 CLI の実行テストを行います。
