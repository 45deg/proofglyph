# proofglyph

依存型理論（λΠ計算 / LF）に基づく OCaml 製の小さな証明検査器です。空白不要の極小な記号言語（proofglyph 言語）で記述された証明を検査します。名前付きの構文から proofglyph 言語を生成する補助言語として hieratic 言語を備えています。

hieratic 言語の入力：

```text
symbol A : Type;
def id (x : A) : A := x;
```

生成される proofglyph 言語のコード（proofglyph にコメント構文はありません）：

```text
*:#0#0>#0$0\!
```

カーネルは de Bruijn index、`Type/Kind`、Π、λ、関数適用、不透明な定数のみを扱います。型の比較には β 同値を用い、登録後の定数本体は展開しません。hieratic の `def` は後続の参照で本体を展開します。展開と β 簡約はコンパイラが行い、生成した項をカーネルが再検査します。`theorem` は展開しない不透明な証明です。`symbol` は未定義の型・記号、`axiom` は信頼する論理規則や数学的公理を宣言します。どちらもカーネルでは前提として数えられます。

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
python3 web/dev.py
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開いて利用します。

## 形式証明と信頼境界 (Rocq)

カーネルの型検査は、導入された公理自体の無矛盾性までは保証しません。算術の信頼する前提には、論理・等式・Peano 公理に加えて、関数型の原始再帰の公理を含みます。演算や述語ごとの定義・導入除去規則は `def` と証明済みの `theorem` にしています。

通常の OCaml 実装とは独立した Rocq 実装と形式証明を [rocq/](rocq/README.md) に収録しています。以下は Rocq 側の保証であり、通常の OCaml 実装自体の正しさを形式証明したものではありません。通常の利用に Rocq は不要です。

| 対象 | 保証内容 |
| --- | --- |
| [proofglyph](rocq/proofglyph/README.md) | 宣言的型付けに対する検査器の健全性と、十分な fuel の下での完全性を証明。OCaml コードを抽出して `.pg` を再検査可能 |
| [hieratic](rocq/hieratic/README.md) | 解析・import 展開の仕様との同値性、名前解決・定義の展開・簡約前後の検査の健全性・完全性、`.pg` の符号化・復号の往復性を証明 |
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
- [算術ライブラリ](examples/commons/README.md): Peano・再帰の公理を基礎とする自然数の演算、整除性、二項定理、素数の無限性、$\sqrt{2}$ の無理性など。
- [基本例](examples/basics.ht) / [論理の例](examples/logic.ht) / [フェルマーの小定理の適用例](examples/fermat_application.ht)