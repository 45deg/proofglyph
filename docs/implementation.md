# 実装と検証

[言語仕様](spec.md) に対応する実装の構成と検証手順をまとめる。通常の OCaml 実装、同じ実装を使う Web デモ、独立した Rocq 実装を含む。型付け規則は言語仕様、証明例の解説は [証明カタログ](proofs.md)、形式証明の定理と制限は [Rocq の README](../rocq/README.md) を参照。

## モジュール

| ファイル | 責務 |
| --- | --- |
| `lib/core/term.ml` | AST、shift、捕獲を避ける置換、型表示 |
| `lib/core/kernel.ml` / `.mli` | 型推論、Π の形成、β 同値、検査付きのシグネチャ追加 |
| `lib/proofglyph/reader.ml` | 記号言語の字句読み取りとスタック操作 |
| `lib/proofglyph/writer.ml` | 項から proofglyph 記号列への出力 |
| `lib/hieratic/source.ml` | 名前付きソースの解析、import、糖衣展開、名前解決、出力の再検査 |
| `bin/main.ml` | ファイル I/O、CLI、エラー処理 |
| `test/tests.ml` | 正しい証明、拒否すべき入力、変数操作の回帰テスト |
| `web/browser.ml` | コンパイラ・カーネルの JavaScript API、対応表の保持 |
| `web/app.source.js` / `index.source.html` | Web デモの操作・結果表示・画面 |
| `web/bundle_examples.ml` | 証明例の import 展開、証明カタログの生成 |
| `web/test.cjs` | JavaScript API、証明例、カタログ、ソースマップの実行テスト |

Dune のライブラリは `proofglyph_core`、`proofglyph_language`、`proofglyph_hieratic` に分離する。proofglyph は core に、hieratic は proofglyph と core に依存し、core と proofglyph は hieratic に依存しない。ファイル import に必要な `unix` は hieratic の依存とする。

OCaml API は `Proofglyph_core.Term` / `Kernel`、`Proofglyph_language.Reader` / `Writer`、`Proofglyph_hieratic.Source` から利用する。記号列の出力は `Proofglyph_language.Writer.encode` が担当する。各 API の詳細は後述の [ソース API とソースマップ](#ソース-api-とソースマップ) および各 `.mli` を参照。

カーネルのシグネチャ型は `.mli` で抽象化する。外部から未検査の定数を注入する操作は公開しない。コンパイラはカーネルの内部文脈や正規化器を操作しない。

シグネチャと文脈はリスト、等価性は同一の部分項を省略し、弱頭正規形を再帰的に比較する。型推論は文脈全体と項をキーにして成功した結果だけを再利用し、宣言の登録時にキャッシュを消去する。キャッシュの参照でも fuel を消費する。これにより展開した定義の同じ部分項を繰り返し検査する負荷を抑える。NbE やシグネチャの索引最適化は実装していない。

## 通常実装の検査経路

```text
.ht → Source.load（解析・import 展開）
    → Source.compile_declarations（名前解決・Writer.encode・対応表生成）
    → Reader.run → Kernel（生成した .pg 全体の再検査）
    → Source.compiled → CLI の出力

.pg → Reader.run（字句読み取り・スタック操作・登録）→ Kernel
```

`Source.compile_declarations` は宣言の型と本体を先行するグローバル環境で解決してから名前を追加する。型には Π、本体には λ を追加する糖衣展開は parser 側で行う。1宣言ごとに型と任意の本体、登録命令、改行を出力し、記号列全体を新しいカーネルで再検査する。解析・名前解決の成功だけでは受理としない。

カーネルは適用の関数型を弱頭正規化し、引数型や証明型の一致には β 同値を使う。λ の推論では定義域のソートと本体の推論型を検査し、本体の型が `Kind` なら拒否する。整形式な文脈での推論を前提に、生成した Π 型の再検査は省く。

`assume` / `prove` は検査が成功した後だけ型と由来を追加する。証明本体は保持しない。Reader の途中で失敗すると、それ以前の登録は指定カーネルに残る。CLI は全体の成功後に結果を表示し、コンパイルも全体の成功後に出力する。

fuel は推論・弱頭正規化の呼び出しで消費する共有予算で、既定値は 1,000,000。`check --prelude` は同じカーネルを使うため、本体は prelude の続きの定数番号と残り予算で検査する。構文解析・shift・置換・構造比較はこの予算で完全には制限しない。

## 検証

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/basics.ht -o /tmp/basics.pg
dune exec bin/main.exe -- check /tmp/basics.pg
dune exec bin/main.exe -- compile examples/logic.ht -o /tmp/logic.pg
dune exec bin/main.exe -- check /tmp/logic.pg
dune exec bin/main.exe -- compile examples/fermat_application.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
```

テストには、依存型の文脈 lookup、匿名矢印の深さ、binder 内の置換、β 同値による型一致、深さを変えた項生成、型の不一致、Kind の誤用、CoC だけで許される Π の拒否、不透明性、η の非対応、壊れた記号列、シグネチャの不正参照、fuel の枯渇、前提追加の禁止を含む。

import の検証には、読み込み元からの相対パス、宣言位置での展開、ダイヤモンド依存、シンボリックリンクによる重複、循環、欠落、ファイル名を含む診断、重複宣言、前方参照を含む。ソースマップの元位置・バイト範囲・JSON、型エラーへの元宣言の付記も検査する。CLI で読み込みや型検査が失敗したとき、既存の出力ファイルを維持することも確認する。

分野別ライブラリとフェルマーの利用例は `Source.compile_file` でコンパイルし、記号列をカーネルで再検査する。対象の定理・補題が `Proven` として登録されることを検査する。算術の前提は固定した語彙・Peano 公理・論理規則・定義の許可一覧に限定し、証明ファイルからの公理追加を拒否する。

import の宣言順では定義と証明が交互に現れることがある。テストでは固定した前提を先頭に集めたシグネチャでもコンパイルし直し、証明部分を前提追加禁止で再検証する。数値の等式、範囲条件、合同式の法、平方根の方程式、分母の正値性を取り違えた証明も拒否する。ド・モルガン則の構成的な断片は排中律を除いて検査する。

```sh
dune exec bin/main.exe -- compile examples/commons/logic/propositional.ht -o /tmp/propositional.pg
dune exec bin/main.exe -- check /tmp/propositional.pg
dune exec bin/main.exe -- compile examples/commons/equality.ht -o /tmp/equality.pg
dune exec bin/main.exe -- check /tmp/equality.pg
dune exec bin/main.exe -- compile examples/commons/nat/fermat.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
```

これは実装と証明項の回帰検査であり、カーネル自体の形式的な健全性証明ではない。再帰方程式と述語の導入・除去規則は LF のシグネチャで明示する定義であり、カーネル内に自然数や算術演算の意味を組み込まない。詳細は [証明カタログ](proofs.md) を参照。

## 開発

通常 CLI とライブラリは Dune と OCaml 標準ライブラリ（`Unix.realpath` を使うため `unix` を含む）だけでビルドできる。Web ビルドには js_of_ocaml、形式証明には Rocq と標準ライブラリが必要。Merlin / OCaml LSP は Dune のプロジェクト設定を使う。通常実装の parser は手書きで、Menhir などの parser 生成器は使わない。

新しい糖衣は名前付き AST に展開し、カーネルの規則は変更しない。定数展開、η 同値、CoC、書換え規則を追加する場合は単なる構文変更として扱わず、型理論の仕様変更として検討する。

## ソース API とソースマップ

`Source.parse` / `Source.compile` は文字列を扱い、import を含む入力はファイル読み込み API の使用を求める診断で拒否する。`Source.parse_items` は import と宣言を区別して解析する。`Source.load path` は import を展開した宣言一覧、`Source.compile_file path` は検査済みの記号列・宣言名・ファイル位置付き宣言一覧を返す。

読み込み済み宣言は `Source.compile_declarations` でも検査できる。import の状態は1回の読み込みに閉じ、作業ディレクトリやカーネルの規則は変更しない。

`Source.parse_items_with` / `Source.parse_with` / `Source.load_with` は、出力 AST の構築方法を
`syntax` レコードで受け取る。既存 API は `default_syntax` を使い、従来の名前付き AST を返す。
`rocq/hieratic/adapter.ml` の `raw_syntax` は引数グループと糖衣を保持する AST を作り、既存 parser と抽出 parser の差分テストに使う。Rocq 版 CLI は `rocq/hieratic/HieraticSyntaxImpl.v` の独立した
lexer/parser と `HieraticImportsImpl.v` の有限ファイル集合上の import 展開を抽出して使う。
ファイル I/O・`realpath`・依存表の収集は OCaml に残る。解析・import の独立仕様との
同値性と内部 fuel の十分性を証明し、計算例と既存実装との比較でも検査する。

ソースマップは、元の宣言と生成した proofglyph バイト列の対応を記録する。`Source.compiled.sourcemap` は宣言ごとの定数番号・名前・ソース位置・出力バイト範囲を保持し、`Source.sourcemap_json result` で JSON に直列化する。範囲はエンコード時に記録され、記号列の再検査に成功した場合のみ結果を返す。

`Source.annotate_assembly_error` は宣言のバイト範囲に含まれる診断に元位置と宣言名を添える。範囲外の診断はそのまま返し、コンパイル時の型エラーにも適用する。

`Source.compile_file` の対応表は canonical な絶対パスを持ち、`Source.compile` では `file = null` となる。`Source.parse_items ~file` から渡した宣言には指定したパスが残る。CLI は検査後に sourcemap、記号列の順で書き込む。出力先は既存ファイルの device/inode または親ディレクトリの実体パスとファイル名で比較し、同じ出力先を拒否する。2ファイルの書き込み中の I/O エラーに対する同時更新は保証しない。

## Web デモ

`web/browser.ml` は js_of_ocaml を通じて `globalThis.proofglyph` に `examples`、`compileAt`、`checkMapped`、`check` を公開する。関数は `{ok, output}` を返し、成功した `compileAt` は対応表の JSON 文字列も返す。検証は実行ごとに新しいカーネルで行い、fuel は既定値を使う。入力中の import は拒否する。

`compileAt` は表示用パスを位置情報に付け、呼び出し時に前回の結果を破棄する。`checkMapped` は直近の成功した `compileAt` の出力と完全一致する場合に対応表を使う。違う場合は `cN` 表示へ戻る。`check` は常に対応表を使わない。

デモ用の証明例は `web/bundle_examples.ml` により import を宣言位置に展開して収録される。共通の依存関係は1度だけ含め、自己完結した単一の hieratic ソースとしてブラウザ上で検査できる。

`web/dune` は `examples/` から `examples_data.ml` を生成して JavaScript に組み込み、画面・操作スクリプト・カタログを配信物にコピーする。`--catalog` は `docs/proofs.md` の `<!-- proof-catalog:start -->` と `<!-- proof-catalog:end -->` で囲まれた表とソースの宣言を照合し、名前・パス・行を持つカタログを生成する。見出しの文言は生成処理に影響しない。表の分野・命題名はカタログの表示名となり、変更するとキーも変わる。カタログは自動更新せず、証明例や表の変更時に生成し直す。

`web/app.source.js` はカタログを配信元から取得し、分類別の選択肢を作る。ソース編集・proofglyph 編集で対応表と結果を無効化する。コンパイル成功後は自動で検査し、API が返す全宣言の結果から `proven` 宣言の成功表示を作る。ブラウザ内で完結するのは入力のコンパイル・検査である。

```sh
dune exec web/bundle_examples.exe -- --catalog examples > /tmp/proofglyph-catalog.json
cp /tmp/proofglyph-catalog.json examples/catalog.json
dune build @web/browser
node web/test.cjs
```

`web/test.cjs` は同梱した全証明例と不正 import の拒否、カタログと文書・宣言位置の一致、宣言名表示・型エラー・古い対応表へのフォールバックを確認する。Node.js 上の実行テストであり、画面のレイアウトやブラウザ操作の検証は含まない。

## Rocq 実装と形式証明

| ディレクトリ | 実装・証明の構成 |
| --- | --- |
| `rocq/proofglyph/` | AST、宣言的型付け、置換・型保存・合流性・強正規化、`WeakCheckerImpl.v` とその健全性・完全性、OCaml 抽出と手書き CLI |
| `rocq/hieratic/` | 糖衣 AST・展開、名前解決・宣言変換、proofglyph 側の共通 codec、独立した lexer/parser・import 展開、抽出コードと I/O アダプター |
| `rocq/calculi/` | 独立した NK・LK、固定 LF シグネチャとの対応、LK のカット除去、直接 AST からの proofglyph 出力と再検査 |
| `rocq/zfc/` | 一階論理・ZFC の証明体系、式の符号化、固定シグネチャとの翻訳・復元、生成証明と Russell の例の再検査 |

`proofglyph` は `WeakChecker.v` で健全性・完全性を証明した弱頭検査器を抽出して使い、通常の OCaml カーネルを呼ばない。proofglyph 側の共通抽出 codec が宣言列を構築する。任意バイト列の復号と独立した字句・スタック仕様の対応を証明している。I/O・CLI・index 上限の事前検査は未検証。

`hieratic` の実行経路は次のとおり。

```text
.ht → adapter.ml（I/O・realpath・依存表収集）
    → prepare_files / parse_hieratic / load_hieratic（抽出 parser・パス対応表適用・import 展開）
    → desugar_program → lower → check_program → encode_proofglyph

.pg → decode_proofglyph → check_program
```

CLI は通常実装の lexer/parser・import loader・名前解決・カーネルを呼ばない。`adapter.ml` に残る通常実装の AST 変換・`raw_syntax` は差分テスト用である。字句・文法・import の独立仕様との対応と内部 fuel の十分性、保存したバイト列から proofglyph 出力・再検査までの形式証明がある。全経路は `FileSpec` / `FileImpl` / `FileCompile` に分ける。言語理論は実装に依存せず、実装は対応証明に依存しない。`rocq/test_layers.py` がこの境界を検査する。

Rocq 版の fuel は再帰の深さで、両 CLI の既定値は2048、指定範囲は1〜100000。proofglyph は入力 index も100000以下に制限する。hieratic の codec は Rocq の自然数を扱う。抽出では自然数を機械整数に置き換えない。十分な fuel による完全性は CLI 上限や実機資源内での成功を保証しない。

```sh
make -C rocq verify
make -C rocq test
```

ルートの Makefile は proofglyph、hieratic、calculi、zfc の順で各サブプロジェクトを検証する。個別には `make -C rocq/proofglyph test` などを使う。`ROCQ` / `OCAMLC` で実行ファイルを指定できる。生成した証明データ、Rocq コンパイル結果、抽出コード・CLI は各ディレクトリの `_build/` に配置する。

`verify` は証明をコンパイルし、主要定理の `Print Assumptions` と `rocq check` による再検査を行う。`test` はこれに加えて抽出 CLI・生成された proofglyph の実行テストや通常実装との比較を行う。形式証明と差分テストは保証が異なり、後者だけで通常実装の正しさは証明されない。

NK・LK と ZFC の同値性は、それぞれ指定した固定シグネチャ上の AST に対する定理である。生成した proofglyph バイト列とその AST の一般的な対応、通常の OCaml 実装自体の正しさ、公理の無矛盾性は保証しない。Rocq のカーネル・抽出機構、OCaml コンパイラ・実行系、I/O は信頼境界に残る。詳しい定理と制限は [Rocq の README](../rocq/README.md) を参照。

## 透明な定義の展開

通常の Hieratic コンパイラは `def` の閉じた本体を後続の参照へ展開し、β 簡約して出力する。簡約前の項も検査して、消去される不正な引数を拒否する。生成 `.pg` は独立した reader とカーネルで再検査する。`theorem` は不透明な参照を保持する。`symbol` と `axiom` はともに `:` で登録する前提だが、ライブラリでは語彙と証明を持たない原理を区別する。

ブラウザ API の `type` は展開後の検査済み型、`surfaceType` は同じコンパイル結果に対応する元の名前付きの型であり、表示は後者を優先する。直接編集した `.pg` には `surfaceType` を付けない。Rocq 版も抽出した解析器・展開器・β 簡約器・検査器を使用する。`Elaboration.v` は透明な定義の展開関係を定式化し、簡約前後の型検査を含むコンパイルの健全性・完全性を証明する。元の名前付きの型の表示やブラウザ UI は証明対象に含まれない。
