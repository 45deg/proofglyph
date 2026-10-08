# tinyprover

依存型理論（λΠ計算 / LF）に基づく OCaml 製の小さな証明検査器です。空白不要の極小な記号言語（pa言語）で記述された証明を検査します。名前付きの構文から pa言語を生成する補助言語として tp言語を備えています。

```text
// tp言語 (入力)
axiom A : Type;
def id (x : A) : A := x;
```

```text
// pa言語 (検査対象)
*:#0#0>#0$0\!
```

Kernel は de Bruijn インデックス、`Type/Kind`、Π、λ、関数適用、不透明な定数のみを扱います。型の比較には β 同値を用い、登録後の定数本体は展開しません。

## ビルドと実行

OCaml と Dune 3.0 以上が必要です（外部ライブラリへの依存はありません）。

```sh
dune build bin/main.exe
dune runtest
```

### CLI の使い方

```sh
# tp言語をコンパイルして pa言語を出力
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa

# pa言語を検査
dune exec bin/main.exe -- check /tmp/basics.pa

# 各定数の型・前提・証明済みの一覧を表示
dune exec bin/main.exe -- inspect /tmp/basics.pa
```

- `-o FILE`: 出力先を指定（省略時は標準出力）。検査成功時のみ書き込みます。
- `--sourcemap FILE`: 宣言単位の対応表を JSON 形式で出力します。
- `--prelude FILE`: 前提（公理）を別ファイルから読み込み、対象ファイル内での新たな公理導入（`:`）を禁止します。
- `--no-axioms`: ファイル内での公理導入（`:`）を禁止します。
- `--fuel N`: 検査ステップ数の上限（既定値: 1,000,000）。

tp言語では `import "相対パス.tp";` でファイルを分割できます。ルートファイルを `compile` すると、依存関係を展開した単一の `.pa` ファイルが生成されます。

## Web デモ

ブラウザ上で動作する Web デモです。コンパイラと Kernel を JavaScript に変換しており、ブラウザ内のみでコンパイルと検査を実行できます。

```sh
opam install js_of_ocaml js_of_ocaml-compiler
dune build @web/browser
python3 -m http.server 8765 --bind 127.0.0.1 --directory _build/default/web
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開いて利用します。成果物（`index.html`, `app.js`, `browser.bc.js`, `catalog.json`）は静的ファイルとして配信可能です。

## 形式証明と信頼境界 (Rocq)

Kernel の型検査は、導入された公理自体の無矛盾性までは保証しません。

また、本実装とは独立した Rocq 実装と形式証明を [rocq/](rocq/README.md) に収録しています（通常の利用に Rocq は不要です）。

| 対象 | 保証内容 |
| --- | --- |
| [pa](rocq/pa/README.md) | 宣言的型付けに対する検査器の健全性・完全性を証明。OCaml コードを抽出して `.pa` を再検査可能 |
| [tp](rocq/tp/README.md) | 解析・import 展開から `.pa` 出力までの健全性・完全性、codec の往復性を証明 |
| [命題論理 NK・LK](rocq/calculi/README.md) | 自然演繹 NK・シークエント計算 LK の導出と tinyprover 証明項の対応、LK のカット除去を証明 |
| [ZFC](rocq/zfc/README.md) | 独立した ZFC 公理系と tinyprover に受理される証明項の存在の同値性を証明 |

```sh
make -C rocq verify
make -C rocq test
```

## ドキュメントと例

- [仕様](docs/spec.md): 型理論、pa言語・tp言語の文法、型付けと等価性の言語仕様。
- [実装の構成](docs/implementation.md): モジュール分割、検査パイプライン、ソースマップ。
- [証明カタログ](docs/proofs.md): 収録されている証明例（論理・等式・自然数・整数論）の解説。
- [算術ライブラリ](examples/commons/README.md): Peano 公理から導出した自然数の演算、整除性、二項定理、素数の無限性、$\sqrt{2}$ の無理性など。
- [基本例](examples/basics.tp) / [論理の例](examples/logic.tp) / [フェルマーの小定理の適用例](examples/fermat_application.tp)

## 開発環境

Dune によりエディタ用設定が生成されるため、`dune build` 後は Merlin や OCaml LSP で開発できます。
