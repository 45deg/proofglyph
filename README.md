# tinyprover

空白不要の記号言語（pa言語）で記述した証明を検査する、OCaml 製の小さな証明検査器です。pa言語は証明の記述・検査を行うコアの記号言語で、tp言語は名前付き λΠ 構文から pa言語を生成するための補助言語です。Kernel は de Bruijn インデックス、`Type/Kind`、Π、λ、関数適用、不透明な定数を扱います。

型の比較には β 同値を使います。`def` と `theorem` は同じ型検査を受け、登録後の本体は展開されません（不透明）。LF 系の体系であり、CoC や暗黙引数、メタ変数（穴）、タクティクスなどは備えていません。

```text
axiom A : Type;
def id (x : A) : A := x;
```

```text
*:#0#0>#0$0\!
```

## ビルドと実行

OCaml と Dune 3.0 以上が必要です。CLI は外部 OCaml ライブラリへの依存がありません（OCaml 5.5.0 / Dune 3.24.1 で検証済み）。

```sh
dune build bin/main.exe
dune runtest
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa
dune exec bin/main.exe -- check /tmp/basics.pa
dune exec bin/main.exe -- inspect examples/identity.pa
```

`compile` は出力する記号列を再読み込みして Kernel で検査します。検査に失敗した場合は出力先ファイルを更新しません。`-o` を省略した場合は標準出力に出力します。

`--sourcemap FILE` を指定すると、宣言単位の対応表を JSON で保存します。import 先を含む元ファイル・行・列・宣言名・定数番号と、出力のバイト範囲を記録します。

```sh
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa --sourcemap /tmp/basics.pa.map
```

`check` と `inspect` は全宣言を検査し、各定数の型と `assumption` / `proven`、宣言数と前提数を表示します（`proven` は指定した型で正しく検査されたことを表し、前提なしの無条件の証明を意味するわけではありません）。

信頼する前提を別ファイルに分ける場合は、次のように指定します。対象ファイルの定数番号は prelude の続きから割り振られます。

```sh
printf '*:' > /tmp/prelude.pa
printf '%s' '#0#0>#0$0\!' > /tmp/proof.pa
dune exec bin/main.exe -- check /tmp/proof.pa --prelude /tmp/prelude.pa
```

`--prelude` を指定すると、対象ファイル内での新たな前提（`:`）の導入を禁止します。`--no-axioms` は prelude なしで前提の導入を禁止します。

tp言語では、宣言の位置に `import "相対パス.tp";` を記述してファイルを分割できます。パスは読み込み元ファイルを基準に解決され、重複する依存ファイルは1度だけ読み込まれます。

```text
import "commons/nat/addition.tp";
```

ルートファイルを通常どおり `compile` すると、依存する全宣言を含む単一の `.pa` ファイルが生成されます。

各コマンドの `--fuel N` は検査ステップ数の上限（既定値: 1,000,000）です。prelude と本体で上限を共有し、ステップ数を超過した場合は検査失敗となります。CLI のオプション・診断・終了コードは[仕様書](docs/spec.md#6-cli-と資源制限)を参照してください。

## Webデモ

`web/` に、ブラウザ上で動作する Web デモがあります。js_of_ocaml によりコンパイラと Kernel が JavaScript に変換されており、外部サーバーを使わずにブラウザ上で tp言語のコンパイルや pa言語の検査を実行できます。

```sh
opam install js_of_ocaml js_of_ocaml-compiler
dune build @web/browser
python3 -m http.server 8765 --bind 127.0.0.1 --directory _build/default/web
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開くと利用できます。
ビルド成果物（`index.html`, `app.js`, `browser.bc.js`, `catalog.json`）は静的ホスティングでそのまま配信可能です。

- **3ペイン表示**: pa言語（記号列）、検査結果、tp言語のソースを並べて表示・編集できます。
- **証明例の読み込み**: [証明カタログ](docs/proofs.md#実装した証明) の証明例を、入門・論理・等式・自然数・整数論に分けたドロップダウンから選択できます。恒等関数や依存型の入門例から、強い帰納法・除法の原理・ユークリッドの補題まで収録しています。依存関係はインライン展開されているため、単一ファイルとしてそのまま検査できます。
- **ソースマップ連携**: コンパイル時の sourcemap により、検査結果の定数を元の宣言名で表示し、型エラー時には対応する行・列・宣言名を報告します。
- **構文リファレンス**: 画面下部に tp言語と pa言語の構文一覧およびコード対応例を表示します。

Web デモ上での直接入力では `import` は使用できないため、展開済みのソースを入力してください。また、pa言語の記号列を直接編集して検査した場合、定数名は `cN` 形式で表示されます。

証明例の追加・変更時は、次の手順でカタログを更新して再ビルドします。

```sh
dune exec web/bundle_examples.exe -- --catalog examples > /tmp/tinyprover-catalog.json
cp /tmp/tinyprover-catalog.json examples/catalog.json
dune build @web/browser
node web/test.cjs
```

## 仕様と例

- [仕様 v0.3](docs/spec.md): 文法、束縛、型付け、登録、CLI、公開 API、Web デモ、Rocq 版の保証と信頼境界。
- [実装の構成](docs/implementation.md): モジュール、検査経路、ソースマップ、Web・Rocq の構成と検証手順。
- [基本例](examples/basics.tp): 恒等関数、依存型、β 同値。
- [論理の例](examples/logic.tp): 含意の導入・除去。
- [証明カタログ](docs/proofs.md): 入門・論理・等式・自然数・整数論の証明例。算術の定理は Peano 公理・論理規則・明示した定義から導出し、分野別のライブラリにまとめています。
  - [論理](examples/commons/logic/propositional.tp): 含意、連言、選言、対偶、構成的なド・モルガン則。古典論理と量化は別モジュール。
  - [等式](examples/commons/equality.tp): 反射律と置換から対称律・推移律・関数による保存を導出。
  - [ライブラリの構成](examples/commons/README.md): 帰納法による算術、偶奇、有限和、整除性、合同式、二項定理、素数の無限性、√2 の無理性。証明済み補題を使ったフェルマーの小定理も収録。
- [フェルマーの小定理の証明と利用例](examples/fermat_application.tp): ライブラリを import してフェルマーの小定理を適用する具体例（[解説](docs/proofs.md#フェルマーの小定理)）。

## 形式証明と信頼境界

型の正しさを検査しても、任意に追加した前提の無矛盾性までは保証しません。なお、本リポジトリの OCaml 実装（コンパイラ・Kernel）そのものの形式検証は行っていません。

独立した Rocq 実装と形式証明は [rocq/](rocq/README.md) にまとめています。通常の OCaml ビルドに Rocq は不要です。

| 対象 | 保証・用途 |
| --- | --- |
| [pa](rocq/pa/README.md) | 宣言的型付けに対する検査器の健全性・十分な fuel による完全性を証明し、OCaml に抽出して `.pa` を独立に再検査 |
| [tp](rocq/tp/README.md) | バイト列・有限ファイル表から `.pa` 出力までの健全性・完全性、解析・import の仕様との対応、codec の往復性・出力再検査を証明 |
| [命題論理 NK・LK](rocq/calculi/README.md) | 固定シグネチャ上で導出と LF 証明項・AST 検査器の受理との対応を証明。LK のカット除去も証明 |
| [ZFC](rocq/zfc/README.md) | 閉じた式と固定シグネチャについて、独立した ZFC 証明体系と AST 検査器に受理される pa 証明項の存在の同値性を証明 |

```sh
make -C rocq verify
make -C rocq test
rocq/pa/_build/pa check examples/identity.pa
rocq/tp/_build/tp check examples/basics.tp
```

Rocq 版の実行には Rocq・標準ライブラリ、OCaml、Dune、Make が必要で、実行テストには Python 3 も使います。Rocq 版 CLI（`pa`, `tp`）の既定 fuel は 2048（指定範囲: 1〜100000）です。ここでの fuel は再帰の深さを表し、通常の OCaml 版 CLI のステップ数とは異なります。

ファイル I/O や実体パスの解決、Rocq の抽出機構、OCaml 実行系などは信頼境界（未検証の前提）に残ります。証明範囲と制限の詳細は[仕様書の第9節](docs/spec.md#9-rocq-実装と形式証明)および各ディレクトリの README を参照してください。

## エディタ

Dune により設定が提供されるため、`dune build` の実行後は Merlin や OCaml LSP 対応エディタですぐに開発できます。
