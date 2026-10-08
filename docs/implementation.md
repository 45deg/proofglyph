# 実装と検証

## モジュール

| ファイル | 責務 |
| --- | --- |
| `lib/core/term.ml` | AST、shift、捕獲を避ける置換、型表示 |
| `lib/core/kernel.ml` / `.mli` | 型推論、Π の形成、β 同値、検査付きのシグネチャ追加 |
| `lib/pa/reader.ml` | 記号言語の字句読み取りとスタック操作 |
| `lib/pa/writer.ml` | 項から pa 記号列への出力 |
| `lib/tp/source.ml` | 名前付きソースの解析、import、糖衣展開、名前解決、出力の再検査 |
| `bin/main.ml` | ファイル I/O、CLI、エラー処理 |
| `test/tests.ml` | 正しい証明、拒否すべき入力、変数操作の回帰テスト |

Dune のライブラリは `tinyprover_core`、`tinyprover_pa`、`tinyprover_tp` に分離する。pa は core に、tp は pa と core に依存し、core と pa は tp に依存しない。ファイル import に必要な `unix` は tp の依存とする。

OCaml API は `Tinyprover_core.Term` / `Kernel`、`Tinyprover_pa.Reader` / `Writer`、`Tinyprover_tp.Source` から利用する。従来の `Term.encode` は `Tinyprover_pa.Writer.encode` に移動した。

Kernel のシグネチャ型は `.mli` で抽象化する。外部から未検査の定数を注入する操作は公開しない。コンパイラは Kernel の内部文脈や正規化器を操作しない。

初版では監査しやすさを優先し、シグネチャと文脈はリスト、等価性は正規形の構造比較とする。大きなライブラリ向けの共有、キャッシュ、NbE、索引最適化は未実装。

## 検証

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/basics.tp -o /tmp/basics.pa
dune exec bin/main.exe -- check /tmp/basics.pa
dune exec bin/main.exe -- compile examples/logic.tp -o /tmp/logic.pa
dune exec bin/main.exe -- check /tmp/logic.pa
dune exec bin/main.exe -- compile examples/fermat_application.tp -o /tmp/fermat.pa
dune exec bin/main.exe -- check /tmp/fermat.pa
```

テストには、依存型の文脈 lookup、匿名矢印の深さ、binder 内の置換、β 同値による型一致、深さを変えた項生成、型の不一致、Kind の誤用、CoC だけで許される Π の拒否、不透明性、η の非対応、壊れた記号列、シグネチャの不正参照、fuel の枯渇、前提追加の禁止を含む。

import の検証には、読み込み元からの相対パス、宣言位置での展開、ダイヤモンド依存、シンボリックリンクによる重複、循環、欠落、ファイル名を含む診断、重複宣言、前方参照を含む。CLI で読み込みや型検査が失敗したとき、既存の出力ファイルを維持することも確認する。

44個の分野別ライブラリとフェルマーの利用例は `Source.compile_file` でコンパイルし、記号列を Kernel で再検査する。以前の未証明補題と各候補が `Proven` として登録されることを検査する。算術の前提は固定した語彙・Peano 公理・論理規則・定義の許可一覧に限定し、証明ファイルからの公理追加を拒否する。

import の宣言順では定義と証明が交互に現れることがある。テストでは固定した前提を先頭に集めたシグネチャでもコンパイルし直し、証明部分を前提追加禁止で再検証する。数値の等式、範囲条件、合同式の法、平方根の方程式、分母の正値性を取り違えた証明も拒否する。ド・モルガン則の構成的な断片は排中律を除いて検査する。

```sh
dune exec bin/main.exe -- compile examples/commons/logic/propositional.tp -o /tmp/propositional.pa
dune exec bin/main.exe -- check /tmp/propositional.pa
dune exec bin/main.exe -- compile examples/commons/equality.tp -o /tmp/equality.pa
dune exec bin/main.exe -- check /tmp/equality.pa
dune exec bin/main.exe -- compile examples/commons/nat/fermat.tp -o /tmp/fermat.pa
dune exec bin/main.exe -- check /tmp/fermat.pa
```

これは実装と証明項の回帰検査であり、Kernel 自体の形式的な健全性証明ではない。再帰方程式と述語の導入・除去規則は LF のシグネチャで明示する定義であり、Kernel 内に自然数や算術演算の意味を組み込まない。詳細は [証明カタログ](proofs.md) を参照。

## 開発

Dune と OCaml 標準ライブラリ（`Unix.realpath` を使うため `unix` を含む）だけでビルドできる。Merlin / OCaml LSP を利用する場合は Dune のプロジェクト設定を使う。追加の生成器、Menhir、パッケージマネージャー固有のセットアップは不要。

新しい糖衣は名前付き AST に展開し、Kernel の規則は変更しない。定数展開、η 同値、CoC、書換え規則を追加する場合は単なる構文変更として扱わず、型理論の仕様変更として検討する。

## ソース API とソースマップ

`Source.parse` / `Source.compile` は文字列を扱い、import を含む入力はファイル読み込み API の使用を求める診断で拒否する。`Source.parse_items` は import と宣言を区別して解析する。`Source.load path` は import を展開した宣言一覧、`Source.compile_file path` は検査済みの記号列・宣言名・ファイル位置付き宣言一覧を返す。

読み込み済み宣言は `Source.compile_declarations` でも検査できる。import の状態は1回の読み込みに閉じ、作業ディレクトリや Kernel の規則は変更しない。

`Source.compiled.sourcemap` は宣言ごとの定数番号・名前・ソース位置・出力バイト範囲を保持し、`Source.sourcemap_json result` で JSON に直列化する。範囲はエンコード時に記録され、記号列の再検査に成功した場合のみ結果を返す。

`Source.annotate_assembly_error` は宣言のバイト範囲に含まれる診断に元位置と宣言名を添える。範囲外の診断はそのまま返し、コンパイル時の型エラーにも適用する。

## Webデモ

`web/browser.ml` は js_of_ocaml を通じてコンパイラと Kernel を JavaScript に公開する。`compileAt` はコンパイル結果とソースマップを返し、`checkMapped` はコンパイル出力と入力が一致する場合に対応表を用いて宣言名付きで結果を表示する。検証は実行ごとに新しい Kernel で行う。

デモ用の証明例は `web/bundle_examples.ml` により import を宣言位置に展開して収録される。共通の依存関係は1度だけ含め、自己完結した単一の tp ソースとしてブラウザ上で検査できる。
