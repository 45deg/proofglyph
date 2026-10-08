# rocq4tp

tinyprover の名前付き AST から、`rocq4pa` の核心言語への変換と `.pa` バイト列の
符号化・復号を Rocq で実装・証明します。変換器と codec を OCaml に抽出し、
既存の Rocq 製型検査器へ接続しています。

糖衣展開に加え、`.tp` の字句解析・構文解析・有限ファイル集合上の import 展開も
Rocq で実装し、抽出したコードを CLI で使います。ファイル I/O と canonical なパスの
解決は OCaml が担当します。既存の保証は糖衣 AST から `.pa` 出力・再検査までで、
lexer/parser と独立した文法との同値性、import 展開の一般的な正しさは未証明です。

## ビルドと実行

親プロジェクトと同じ OCaml・Dune、および `rocq4pa` と同じ Rocq・標準ライブラリ、
Make、テスト用の Python 3 が必要です。追加パッケージは不要です。

```sh
make -C rocq4tp
rocq4tp/_build/rocq4tp check examples/basics.tp
rocq4tp/_build/rocq4tp check examples/fermat_application.tp
rocq4tp/_build/rocq4tp compile examples/basics.tp -o /tmp/basics.pa
rocq4tp/_build/rocq4tp check-pa /tmp/basics.pa
make -C rocq4tp test
```

`make verify` は証明のコンパイル、`Print Assumptions`、`rocq check` による再検査、
OCaml コードの抽出を行います。`ROCQ` と `OCAMLC` は上書きできます。
生成物は `_build/` 内に置き、親の通常の `dune build` に Rocq 依存を追加しません。

CLI は次のコマンドを受け付けます。

```text
check SOURCE.tp [--no-axioms] [--fuel N]
compile SOURCE.tp [-o OUTPUT.pa] [--no-axioms] [--fuel N]
check-pa INPUT.pa [--no-axioms] [--fuel N]
```

`compile` は型検査に成功した宣言列を空白のない `.pa` として出力します。
`-o` を省くと標準出力へ書きます。入力・名前解決・型検査・ポリシー・fuel による
失敗時は出力ファイルを書き換えません。書き込み中の I/O 障害に対する原子的更新は保証しません。
`check-pa` は Rocq から抽出した復号器と型検査器を使います。
`--no-axioms` は import された宣言も含めて公理を禁止します。prelude 指定は未対応です。
終了コードは成功0、入力・検査・資源エラー1、使用法エラー2です。
`.pa` の入力不正・名前解決・型付け・公理ポリシー・fuel 不足による拒否は、現在は共通の診断になります。

## 実装と仕様

```text
.tp ファイル
  → adapter.ml                 OCaml：ファイル I/O・realpath・依存ファイルの収集
  → parse_tp                   Rocq 抽出：字句解析・構文解析、糖衣 AST
  → load_tp                    Rocq 抽出：import グラフの展開
  → desugar_program             Rocq 抽出：糖衣展開
  → lower                       Rocq 抽出：名前解決・宣言変換
  → Rocq4pa.check_program        Rocq 抽出：型検査
  → encode_pa                   Rocq 抽出：.pa バイト列

.pa バイト列
  → decode_pa                   Rocq 抽出：字句解析・スタック実行・宣言列構築
  → Rocq4pa.check_program        Rocq 抽出：型検査
```

CLI の実行経路は既存の `Source.lex`、parser、import loader、`Source.resolve`、
`Source.compile`、OCaml カーネルを呼びません。
それらを含むライブラリにはリンクしますが、既存の名前解決を使うのは差分テストだけです。

`Desugar.v` の `raw_expr` は矢印、適用、`forall`、`fun` を区別し、`parameters` は
`(x y : A)` のグループと型注釈を保持します。グループは少なくとも1つの名前を持ちます。
`desugar` は矢印を匿名 Π に、`forall` / `fun` を名前付き Π / λ の列に変換します。
型注釈の内部にある糖衣も再帰的に展開します。`expands` / `expands_parameters` は、
この変換の独立した帰納的仕様です。

`(x y : A)` は `(x : A) (y : A)` に展開し、型注釈を各位置にコピーします。
名前解決はその後で行うため、2個目の型注釈は1個目の binder がある環境で解決されます。
シャドーイングがある場合もこの逐次束縛規則を保ち、`split_parameter_group` が
グループを分けた表記との一致を保証します。

`TpSyntax.v` の `lex_tp` / `parse_tp` は ASCII 識別子、予約語、行コメント、
エスケープなしの import パスを扱う再帰下降 parser です。適用は左結合、矢印は
右結合で、適用が優先します。宣言の引数は型に `RForall`、本体に `RLambda` を
組み立て、グループは展開せず保持します。引数なしでは `PNil` を使います。
解析用の内部 fuel は入力長から計算し、型検査の `--fuel` とは独立です。

`TpImports.v` の `load_tp` は canonical なファイル名と item 列の有限表を受け取り、
宣言位置で深さ優先に展開します。active 列で循環を拒否し、読み込み済み列で
ダイヤモンド依存を重複排除します。表に存在しない依存も拒否します。
OCaml は各ファイルを一度解析し、相対パスを実体ファイルのディレクトリから解決して
表を用意します。循環判定は抽出された関数が行います。
構文エラーは対象ファイル名付きの共通診断で、現在は行・列を保持しません。
複数のエラーがある場合、依存表の収集時の読み込み・解析エラーが先に報告されることがあります。

通常の OCaml CLI / Web とその `Source` API は変更していません。
`adapter.ml` の `raw_syntax` は既存 parser との比較テストにだけ使います。

`Surface.v` の項は `Source.expr` に対応します。矢印は `Product None` で、
匿名 binder も de Bruijn の深さに数えます。局所変数を先に探し、最も内側の名前を優先します。
型注釈は binder の導入前、本体は導入後の環境で解決します。
グローバル名は登録順に並べ、その位置が定数番号になります。

`Compile.v` は重複名を拒否し、宣言の型・本体をそれ以前のグローバル環境で解決してから
名前を追加します。そのため未知名、自己参照、前方参照を拒否します。
`None` の本体は `Assume`、`Some` の本体は `Prove` に変換します。
`def` と `theorem` は既存の AST の段階ですでに同じ構造であり、検査後も定数は不透明です。

実装関数とは別に、最近傍の束縛を表す `binds`、項の翻訳関係 `resolves`、
宣言列の翻訳関係 `translates` を帰納的に定義しています。
これらは成功した実装関数や型検査器によって定義した関係ではありません。

`PaCodec.v` は命令列、十進数の読み書き、バイト列の字句解析、スタック機械を定義します。
`$` / `#` の直後には1桁以上の十進数字が必要で、連続する数字を最長一致で読みます。
先頭0を許し、空白・タブ・CR・LF はトークン間だけで無視します。
未知のバイト、スタック不足、登録時の余分な項、EOF の残りスタックは拒否します。
`decode_pa` は型検査をしません。たとえば `^:` は `Assume tKind` に復号されますが、
`check_pa` は型検査で拒否します。

codec は Rocq の自然数全体を扱います。既存 OCaml reader の機械整数上限や
`rocq4pa` CLI の index 上限100000と同じ数値制限は設けていません。
巨大な番号の実行は時間・メモリ制限を受けます。字句解析の内部 fuel は入力のバイト長で与え、
CLI の型検査用 `--fuel` とは分けています。

## 証明した保証

| 定理 | 保証 |
| --- | --- |
| `desugar_correct` / `desugar_parameters_correct` | 糖衣展開と独立した展開仕様が同値 |
| `expansion_unique` | 展開結果が一意 |
| `split_parameter_group` | 複数名のグループと逐次グループの展開結果が一致 |
| `desugar_program_correct` | 宣言列全体の展開と仕様が同値 |
| `desugar_names` / `desugar_kinds` | 宣言名と公理／証明の種類を順序どおり保存 |
| `resolve_correct` | 名前解決の成功と宣言的な翻訳関係が同値 |
| `resolves_unique` | 項の翻訳結果が一意 |
| `resolve_scoped` | 局所変数・定数の番号が環境の範囲内 |
| `resolves_extend_globals` | 後続のグローバル名を追加しても、成功済みの翻訳は変わらない |
| `lower_correct` / `translates_unique` | 宣言列変換の健全性・完全性・一意性 |
| `translates_kinds` / `translates_length` | 宣言順に公理／証明の種類を保存し、宣言数も保存 |
| `translates_distinct` | 変換できるソースの宣言名には重複がない |
| `translates_policy` | 公理禁止ポリシーが変換の前後で一致 |
| `translates_scoped` | 各宣言の型・本体は閉じており、先行定数だけを参照 |
| `compile_sound` | 翻訳関係、宣言的型付け、ポリシー、結果シグネチャの整形式性 |
| `compile_complete` | 翻訳可能で型が正しくポリシーを満たす宣言列は、十分な fuel で受理 |
| `compile_monotone` | 成功後に fuel を増やしても結果が変わらない |
| `compile_correct` | ある fuel での成功と、翻訳・ポリシー・型付けの仕様が同値 |
| `lex_instructions_roundtrip` | 命令列をバイト列に符号化すると、十分な内部 fuel で同じ命令列に復号 |
| `term_code_correct` | 項の命令列は既存スタックの上にその項を1つ積む |
| `program_code_correct` | 宣言列の命令列は、空スタックから同じ順序の宣言列を構築 |
| `pa_roundtrip` | `decode_pa (encode_pa ds) = Some ds`。型付け・index 上限の前提なし |
| `encode_pa_injective` | 異なる宣言列が同じバイト列へ符号化されることはない |
| `pa_canonical_roundtrip` | 復号できる入力を再符号化しても復号結果が変わらない |
| `compile_pa_sound` / `compile_pa_complete` | `.pa` 出力まで含めた健全性と、十分な fuel による完全性 |
| `compile_pa_recheck` | 出力したバイト列を同じ fuel・公理ポリシーで再検査すると同じシグネチャを得る |
| `check_pa_sound` | 受理したバイト列の復号結果は型付け・ポリシーを満たし、シグネチャも整形式 |
| `compile_pa_monotone` | fuel を増やしても成功した出力は変わらない |
| `compile_surface_pa_sound` / `compile_surface_pa_complete` | 糖衣を保持した AST から `.pa` までの健全性・十分な fuel による完全性 |
| `compile_surface_pa_recheck` | 糖衣を保持した AST から生成した出力も、同じ fuel で再検査できる |

最終定理は次の形です。

```text
(∃ fuel, compile fuel allow src = Some (ds, Σ))
↔ translates [] src ds
  ∧ source_permitted allow src
  ∧ valid_program [] ds Σ
```

バイト列までの保証は次の形です。

```text
compile_pa fuel allow src = Some (bytes, Σ)
→ ∃ ds,
    bytes = encode_pa ds
    ∧ decode_pa bytes = Some ds
    ∧ translates [] src ds
    ∧ source_permitted allow src
    ∧ valid_program [] ds Σ
    ∧ wf_signature Σ

compile_pa fuel allow src = Some (bytes, Σ)
→ check_pa fuel allow bytes = Some Σ
```

入力の空白や先頭0は符号化時に保存しません。そのため往復性は宣言列について示し、
任意の入力バイト列そのものを復元する等式は主張しません。

`compile_surface_pa_sound` は、糖衣を保持した入力 `raw` からの成功に対して、
上記の `src` と `ds` が存在し、さらに `expands_program raw src` が成立することを示します。
`compile_surface_pa_complete` はこの展開関係・翻訳関係・型付け・ポリシーから、
十分な fuel での成功を導きます。

証明は `rocq4pa` の健全性・宣言的完全性・fuel 単調性を再利用しています。
追加公理・`Admitted` は使いません。`Verification.v` の公開定理の仮定確認は、
すべて `Closed under the global context` になります。

## 実行による検証

`Examples.v` では匿名 binder、局所名のシャドーイング、型注釈のスコープ、
恒等関数の検査、重複・前方・自己参照、型誤り、公理禁止を Rocq 内で確認します。

`make test` は抽出された関数を実行し、リポジトリの全48個の `.tp` ファイルについて、
import 後の糖衣展開と名前解決を既存実装と比較し、宣言列と最終シグネチャを確認します。
グループを保持した AST からの `compile_surface_pa` の結果も照合します。
全48件の出力を既存 writer とバイト単位で比較し、Rocq の復号器・型検査器と既存 reader の
両方で検査します。990件の型付けを要求しない項についても、往復性と writer との一致を確認します。
`PaExamples.v` と実行テストは十進数の桁境界、先頭0、空白、未知バイト、スタック異常、
構文上は正しいが型が不正な宣言、検査失敗時の出力ファイル保持を含みます。
`TpExamples.v` で結合・優先順位、グループ、予約語、空パス、ダイヤモンド依存、
宣言位置、循環・欠落を計算によって確認します。実行テストには不正な字句・文法、
コメント、CRLF、シンボリックリンクと拒否時の出力保持も含めています。
さらに束縛の境界例、不正名、型誤り、公理禁止、fuel 不足を確認し、CLI の
ダイヤモンド import、循環、欠落、構文エラー、オプション、終了コードを検査します。
差分テストは既存実装との一致を確認するもので、既存実装の正しさの証明ではありません。

`DesugarExamples.v` はグループの逐次展開、型注釈でのシャドーイング、匿名矢印の深さ、
型注釈内の糖衣、引数なし、`.pa` までの接続を Rocq 内で確認します。
実行テストでは parser がグループを保持すること、明示的な `forall` / `fun`、
同じグループ内の重複名、入れ子の型注釈についても既存の展開結果と比較します。

## 信頼境界と次の段階

- `.tp` 翻訳に関する定理の入力は糖衣を保持した AST です。識別子の字句規則、
  文法・結合・優先順位、宣言の引数を型と本体の AST に配置する parser の処理、
  import 順序、ファイルの同一性、位置情報は未検証です。
  lexer/parser と import 展開は Rocq 実装に移行しましたが、一般的な正しさの定理はまだありません。
  AST ができた後の複数引数・矢印・Π・λ の展開は検証対象に含まれます。
- `.pa` の符号化・復号の往復性は証明しています。任意入力に対する独立した
  `.pa` 文法との同値性や、既存 OCaml reader/writer との一般的な同値性は未証明です。
- 名前付き言語自身の型付け・置換・α 同値を別に定式化した証明はまだありません。
  現在は宣言的な翻訳関係と核心言語の型付けを組み合わせています。
- Rocq のカーネル・抽出機構、OCaml コンパイラ・実行系、ファイル I/O を信頼します。
  自然数を機械整数へ置き換える抽出指示は使いません。
- fuel の既定値は2048、CLI の指定範囲は1〜100000です。十分な fuel の定理は
  任意の自然数に対するもので、CLI 上限や実機の時間・メモリ内での成功を保証しません。
  1回の拒否は型誤りの証明にはなりません。
- 公理の無矛盾性、既存 OCaml コンパイラ・カーネル自体の正しさは保証しません。

次は独立した `.tp` 文法との対応、解析・import 用 fuel の十分性、
有限のファイル集合上の import 展開の仕様との対応を証明します。
