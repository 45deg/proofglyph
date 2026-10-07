# tinyprover

名前付きの λΠ ソース（tp言語）を、空白不要の記号言語（pa言語）にコンパイルする OCaml 製の小さな証明検査器です。Kernel は de Bruijn index、`Type/Kind`、Π、λ、適用、不透明な定数を扱います。

```text
axiom A : Type;
def id (x : A) : A := x;
```

```text
*:#0#0>#0$0\!
```

## 実行

OCaml と Dune 3.0 以上が必要です。CLI は外部 OCaml ライブラリ不要です。OCaml 5.5.0 / Dune 3.24.1 で検証しています。

```sh
dune build bin/main.exe
dune runtest
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa
dune exec bin/main.exe -- check /tmp/basics.pa
dune exec bin/main.exe -- inspect examples/identity.pa
```

`compile` は出力する記号列を再読み込みして Kernel で検査します。検査に失敗した場合、出力先ファイルを書き換えません。`-o` を省くと標準出力に出します。出力の改行はすべて削除できます。

`--sourcemap FILE` を指定すると、宣言単位の対応表を JSON で保存します。import 先を含む元ファイル・行・列・宣言名・定数番号と、出力のバイト範囲を記録します。

```sh
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa --sourcemap /tmp/basics.pa.map
```

`check` と `inspect` はどちらも全宣言を検査して、各定数の型と `assumption` / `proven` を表示します。証明済み定数の展開は行いません。

信頼する前提を別ファイルに分ける場合は、次のようにします。対象ファイルの定数番号は prelude の続きです。

```sh
printf '*:' > /tmp/prelude.pa
printf '%s' '#0#0>#0$0\!' > /tmp/proof.pa
dune exec bin/main.exe -- check /tmp/proof.pa --prelude /tmp/prelude.pa
```

`--prelude` を指定すると対象ファイル内の `:` を禁止します。`--no-axioms` は prelude なしでも対象ファイルの `:` を禁止します。上位言語では、宣言を書く位置に `import "相対パス.tp";` を置いてファイルを分割できます。パスは読み込み元のファイルを基準に解決し、共通の依存ファイルは1度だけ読み込みます。

```text
import "commons/nat/addition.tp";
```

入口ファイルを通常どおり `compile` すると、依存する全宣言を含む `.pa` が生成されます。

## Webデモ

`web/` に、ブラウザ上で動作するデモがあります。
コンパイラと Kernel を js_of_ocaml で JavaScript に変換しており、外部通信を行わずブラウザ内で完結して動作します。

```sh
opam install js_of_ocaml js_of_ocaml-compiler
dune build @web/browser
python3 -m http.server 8765 --bind 127.0.0.1 --directory _build/default/web
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開くと利用できます。
ビルド成果物（`index.html`, `app.js`, `browser.bc.js`, `catalog.json`）は静的ホスティングでそのまま配信可能です。

- **3ペイン表示**: tp言語（ソース）、pa言語（記号列）、検査結果を並べて表示・編集できます。
- **証明例の読み込み**: [証明カタログ](docs/proofs.md#実装した証明) の証明例をドロップダウンから選択できます。依存関係はインライン展開されているため、単一ファイルとしてそのまま検査できます。
- **ソースマップ連携**: コンパイル時の sourcemap により、検査結果の定数を元の宣言名で表示し、型エラー時には対応する行・列・宣言名を報告します。
- **構文リファレンス**: 画面下部に tp言語と pa言語の構文一覧およびコード対応例を表示します。

証明例の追加・変更時は、次の手順でカタログを更新して再ビルドします。

```sh
dune exec web/bundle_examples.exe -- --catalog examples > /tmp/tinyprover-catalog.json
cp /tmp/tinyprover-catalog.json examples/catalog.json
dune build @web/browser
node web/test.cjs
```

## 仕様と例

- [仕様](docs/spec.md): 文法、束縛、型付け、登録、信頼境界、CLI。
- [実装の構成](docs/implementation.md): モジュール、検証、拡張時の注意点。
- [基本例](examples/basics.tp): 恒等関数、依存型、β 同値。
- [論理の例](examples/logic.tp): 含意の導入・除去。
- [証明カタログ](docs/proofs.md): 論理・等式・自然数・整数論の20候補とフェルマーの小定理。Peano 公理・論理規則・明示した定義から導出し、分野別のライブラリにまとめています。
  - [論理](examples/commons/logic/propositional.tp): 含意、連言、選言、対偶、構成的なド・モルガン則。古典論理と量化は別モジュール。
  - [等式](examples/commons/equality.tp): 反射律と置換から対称律・推移律・関数による保存を導出。
  - [ライブラリの構成](examples/commons/README.md): 帰納法による算術、偶奇、有限和、整除性、合同式、二項定理、素数の無限性、√2 の無理性。証明済み補題を使ったフェルマーの小定理も収録。
- [フェルマーの小定理の証明と利用例](examples/fermat_application.tp): 証明済みの `fermat_sum` を読み込み、和に適用する定理を検査します。二項定理・二項係数の整除性も含めて証明済みのファイルを import します。[証明と前提の説明](docs/proofs.md#フェルマーの小定理)も参照してください。

型の正しさを検査しても、任意に追加した前提の無矛盾性までは保証しません。本実装自体の形式検証も行っていません。

独立した再検査器 [rocq4pa](rocq4pa/README.md) もあります。Rocq で定義した型付け規則に対する
検査の健全性と、整形式な環境で十分な fuel を与えたときの宣言的完全性を証明し、
OCaml に抽出して `.pa` を検査します。既存の OCaml カーネルの
検証ではなく、パーサーや実行系は信頼境界に残ります。親プロジェクトの通常のビルドに Rocq は不要です。

Merlin は Dune が提供する設定を利用できます。`dune build` 後、Merlin 対応エディタまたは OCaml LSP でプロジェクトを開いてください。手書きの `.merlin` は不要です。
