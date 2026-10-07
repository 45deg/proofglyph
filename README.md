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

## ブラウザの3ペイン例

`web/` に、tp → pa → チェック結果を3つの textarea で表示する例があります。
既存の OCaml コンパイラと Kernel を js_of_ocaml で JavaScript に変換し、処理はブラウザ内で完結します。

```sh
opam install js_of_ocaml js_of_ocaml-compiler
dune build @web/browser
python3 -m http.server 8765 --bind 127.0.0.1 --directory _build/default/web
```

[http://127.0.0.1:8765](http://127.0.0.1:8765) を開きます。最初のサンプルは自動で検査されます。
tp を編集したら「コンパイル → 検査」、pa を直接編集したら「pa を検査 →」で実行します。
入力を変更すると前回の検査結果を消し、エラーも結果ペインに表示します。狭い画面では縦に並びます。
3ペインの下には、tp言語とpa言語の文法・記号の説明と、同じ恒等関数を両言語で書いた例を表示します。
コンパイル時の sourcemap を使い、検査結果と型中の定数を元の宣言名で表示します。
型エラーには元ファイル・宣言の行列・宣言名を添え、pa の byte offset も残します。
対応は宣言単位です。tp または pa を編集すると map を無効にし、再コンパイルするまで `c0` などの番号で表示します。

ドロップダウンの「実装した証明」は、[証明カタログ](docs/proofs.md#実装した証明) の表にある21項目を日本語で表示します。
同じファイルにある証明は1つの選択肢にまとめ、選択するとそのファイルの証明をまとめて検査します。
証明例の `import` はビルド時に依存先の宣言へ展開し、共通の依存は1度だけ含めます。
tp ペインには展開済みのソースを表示し、デモでは `import` を使わず、その内容だけでコンパイルします。
sourcemap の行列も表示した展開済みソースに対応します。
[JSON カタログ](examples/catalog.json) の `proofs` は日本語の項目名から宣言名・ファイル・行番号を引く辞書です。
ブラウザは配信された `catalog.json` を読み、選択した名前をこの辞書で引きます。
たとえば `catalog.proofs["整数論：フェルマーの小定理と和への適用"]` で対応する証明の場所を取得できます。
サンプルを追加・変更したら、次の手順でカタログを更新して再ビルドしてください。

```sh
dune exec web/bundle_examples.exe -- --catalog examples > /tmp/tinyprover-catalog.json
cp /tmp/tinyprover-catalog.json examples/catalog.json
dune build @web/browser
node web/test.cjs
```

prelude、ソースマップの出力には対応していません。
ビルド後の `index.html`、`app.js`、`browser.bc.js`、`catalog.json`は静的サーバーで配信できます。
ブラウザ例を含む `dune build` には上記の追加パッケージが必要です。

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

Merlin は Dune が提供する設定を利用できます。`dune build` 後、Merlin 対応エディタまたは OCaml LSP でプロジェクトを開いてください。手書きの `.merlin` は不要です。
