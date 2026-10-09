# proofglyph

依存型理論（λΠ計算 / LF）に基づく OCaml 製の小さな証明検査器です。空白不要の極小な記号言語（proofglyph 言語）で記述された証明を検査します。名前付きの構文から proofglyph 言語を生成する補助言語として hieratic 言語を備えています。

hieratic 言語の入力：

```text
axiom A : Type;
def id (x : A) : A := x;
```

生成される proofglyph 言語のコード（proofglyph にコメント構文はありません）：

```text
*:#0#0>#0$0\!
```

カーネルは de Bruijn インデックス、`Type/Kind`、Π、λ、関数適用、不透明な定数のみを扱います。型の比較には β 同値を用い、登録後の定数本体は展開しません。hieratic の `def` と `theorem` は同じ検査を受け、どちらも不透明な定数として登録されます。

## ビルドと実行

OCaml と Dune 3.0 以上が必要です（外部ライブラリへの依存はありません）。

```sh
dune build bin/main.exe
dune runtest
```

### CLI の使い方

```sh
# hieratic 言語をコンパイルして proofglyph 言語を出力
dune exec bin/main.exe -- compile examples/basics.ht -o /tmp/basics.pg

# proofglyph 言語を検査
dune exec bin/main.exe -- check /tmp/basics.pg

# 各定数の型と由来（前提／証明済み）の一覧を表示
dune exec bin/main.exe -- inspect /tmp/basics.pg
```

- `-o FILE`（`compile`）: 出力先を指定（省略時は標準出力）。検査成功時のみ書き込みます。
- `--sourcemap FILE`（`compile`）: 宣言単位のソースマップを JSON 形式で出力します。
- `--prelude FILE`（`check`）: 前提を別ファイルから読み込み、対象ファイル内での新たな前提登録（`:`）を禁止します。
- `--no-axioms`（`check`）: ファイル内での前提登録（`:`）を禁止します。
- `--fuel N`（全コマンド）: 型推論・弱頭正規化で消費する共有予算（既定値: 1,000,000）。時間やメモリの上限ではありません。

hieratic 言語では `import "相対パス.ht";` でファイルを分割できます。ルートファイルを `compile` すると、依存関係を展開した単一の `.pg` ファイルが生成されます。

## Web デモ

ブラウザ上で動作する Web デモです。コンパイラとカーネルを JavaScript に変換しており、ブラウザ内のみでコンパイルと検査を実行できます。

```sh
opam install js_of_ocaml js_of_ocaml-compiler
dune build @web/browser
python3 -m http.server 8765 --bind 127.0.0.1 --directory _build/default/web
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開いて利用します。成果物（`index.html`, `app.js`, `math.js`, `browser.bc.js`, `catalog.json`）は静的ファイルとして配信可能です。

検査結果には、検査済みの型から生成した数式を表示します。選択した定理を先に表示し、依存する補題・定義は折りたたみます。数式表示には CDN から読み込む KaTeX 0.19.0 を使用し、読み込めない場合は TeX 表記を表示します。コンパイルと証明の検査は引き続きブラウザ内で完結します。

## 形式証明と信頼境界 (Rocq)

カーネルの型検査は、導入された公理自体の無矛盾性までは保証しません。

通常の OCaml 実装とは独立した Rocq 実装と形式証明を [rocq/](rocq/README.md) に収録しています。以下は Rocq 側の保証であり、通常の OCaml 実装自体の正しさを形式証明したものではありません。通常の利用に Rocq は不要です。

| 対象 | 保証内容 |
| --- | --- |
| [proofglyph](rocq/proofglyph/README.md) | 宣言的型付けに対する検査器の健全性と、十分な fuel の下での完全性を証明。OCaml コードを抽出して `.pg` を再検査可能 |
| [hieratic](rocq/hieratic/README.md) | 解析・import 展開の仕様との同値性、名前解決・変換の健全性・完全性、`.pg` の符号化・復号の往復性を証明 |
| [命題論理 NK・LK](rocq/calculi/README.md) | 固定 LF シグネチャ上の証明項と NK・LK の導出の対応、および LK のカット除去を証明 |
| [ZFC](rocq/zfc/README.md) | 閉じた式について、ZFC での証明可能性と固定 LF シグネチャ上の型付き証明項の存在の同値性を証明 |

NK・LK と ZFC の定理は Rocq 内の AST を対象とします。生成した proofglyph バイト列と AST の一般的な対応は未証明です。詳細な保証と信頼境界は各 README を参照してください。

```sh
make -C rocq verify
make -C rocq test
```

## ドキュメントと例

- [仕様](docs/spec.md): 型理論、proofglyph 言語・hieratic 言語の文法、型付けと等価性の言語仕様。
- [実装の構成](docs/implementation.md): モジュール分割、検査パイプライン、ソースマップ。
- [証明カタログ](docs/proofs.md): 収録されている証明例（論理・等式・自然数・整数論）の解説。
- [算術ライブラリ](examples/commons/README.md): Peano 公理から導出した自然数の演算、整除性、二項定理、素数の無限性、$\sqrt{2}$ の無理性など。
- [基本例](examples/basics.ht) / [論理の例](examples/logic.ht) / [フェルマーの小定理の適用例](examples/fermat_application.ht)

## 開発環境

Dune によりエディタ用設定が生成されるため、`dune build` 後は Merlin や OCaml LSP で開発できます。
