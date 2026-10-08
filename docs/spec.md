# tinyprover 仕様 v0.3

更新日: 2026-10-09。リポジトリ内の実装を対象とする。

## 1. 対象

β 同値のみを持つ λΠ 計算を実装する。LF 系の依存型計算であり、CoC ではない。型と証明項には同じ構文を使用する。η 同値、定数の展開、再帰定義、帰納型の組込み、ユーザー定義書換え規則、暗黙引数、穴、単一化、タクティクスは提供しない。

第2〜6節は通常の OCaml 実装の言語・CLI 仕様、第7節は OCaml API、第8節は Web デモ、第9節は独立した Rocq 実装と形式証明の範囲を定める。通常の CLI と Web デモは同じコンパイラ・Kernel を使用する。Rocq 抽出版は別の実装であり、資源制限や診断が異なる。

型・項の AST は次の7種類。

```text
t ::= Type | Kind | Var(n) | Const(n)
    | Pi(t,t) | Lam(t,t) | App(t,t)
```

`n` は非負の整数。定数番号は登録順に0から付ける。Π と λ の第2引数だけが新しい変数を束縛する。`Var(0)` は最も内側の変数。型注釈にも同じ束縛規則が適用される。

## 2. pa言語 (.pa)

```ebnf
program = { token } ;
token = "*" | "^" | "$", natural | "#", natural
      | ">" | "\\" | "@" | ":" | "!" ;
natural = digit, { digit } ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
```

空白、タブ、CR、LF はトークン間で無視する。`$` / `#` と数字の間には入れられない。数字は最長一致で読む。先頭の0は許す。OCaml の `int` の範囲外の番号は拒否する。コメント、別名命令、任意文字の無視はない。

スタックの右端が先頭。

| 命令 | 操作 |
| --- | --- |
| `*` | `S → S Type` |
| `^` | `S → S Kind` |
| `$n` | `S → S Var(n)` |
| `#n` | `S → S Const(n)` |
| `>` | `S A B → S Pi(A,B)` |
| `\` | `S A b → S Lam(A,b)` |
| `@` | `S f x → S App(f,x)` |
| `:` | スタックが厳密に `[A]` のとき前提を登録し、空にする |
| `!` | スタックが厳密に `[A,t]` のとき `t:A` を検査・登録し、空にする |

構築時は型検査しない。登録時に閉じた項として検査する。未知の定数、自由変数、スタック不足、登録時の余分な項、EOF の残りスタック、不正文字はエラー。

```text
*:#0#0>#0$0\!
```

上記は `c0 : Type` を前提として登録し、`λ x:c0. x` を検査して `c1 : Π x:c0. c0` を登録する。

`^` を構築することはできるが、`Kind` 自体には型がないため `^:` は拒否される。

## 3. 型付けと等価性

定数の型を登録する列をシグネチャ（signature）と呼ぶ。`Kind` はカインド（kind）を表し、`Type` と `Kind` を総称してソート（sort）と呼ぶ。

シグネチャ Σ と文脈 Γ の下で `Σ; Γ ⊢ t : A` を判定する。公開 Kernel API の検査は空の文脈から開始する。

- `Type : Kind`。`Kind` には型を与えない。
- 変数は文脈に記録した型を現在の深さへ shift して取り出す。
- 定数は Σ に記録された閉じた型を持つ。
- `A : Type` かつ `Γ,x:A ⊢ B:s`、`s ∈ {Type,Kind}` なら `Π x:A.B : s`。
- `A : Type`、`Γ,x:A ⊢ b:B`、かつ `Π x:A.B` が形成可能なら `λ x:A.b : Π x:A.B`。
- `f : Π x:A.B`、`u:A` なら `f u : B[u/x]`。
- 型の比較では β 同値を認める。この関係を調べる操作を同値判定と呼ぶ。

したがって Π 形成のソートの組は `(Type,Type)` と `(Type,Kind)` のみ。`Π A:Type.A→A` は拒否される。

文脈の型は、その変数を導入する直前の文脈に相対的に格納する。index `n` の型を取得するとき `shift(n+1,0,型)` を行う。

β 簡約は `(λ x:A.b) u → b[u/x]`。置換は捕獲を避け、取り除いた binder に対応する index を調整する。適用の型を調べるときは弱頭正規化、等価性は両辺の完全な β 正規形の構造比較で判定する。α 同値は de Bruijn 表現に吸収される。η 同値、証明無関係性、定数展開はない。

## 4. 定数登録と信頼境界

不透明定数（opaque constant）は、型と由来だけを登録し、定義や証明の本体を展開しない定数である。

`assume A` は、空の文脈で `A` のソートが `Type` または `Kind` であることを検査し、新しい不透明定数を登録する。

`prove A t` は、同じく `A` の整形式性と `t:A` を検査して新しい不透明定数を登録する。失敗した宣言は登録しない。いずれも自分自身や後続の定数を参照できない。

登録済み定数には型と由来 (`Assumption` / `Proven`) を保持する。証明項は Kernel のシグネチャには残さない。独立した再検証には入力ファイルと prelude を保存する。`Proven` は検査に成功したという意味であり、前提なしという意味ではない。推移的な前提依存の一覧は計算しない。

前提は理論の公理・推論規則に相当する。Kernel は前提を含む理論の無矛盾性を判定しない。固定理論では信頼する prelude の後の `:` を禁止する。

上位コンパイラの出力は記号言語の reader と Kernel で再検査する。コンパイラの不具合だけで型の不正な証明は受理されないが、別の整形式な命題・前提に翻訳される可能性はこの再検査では除けない。公開する定理と前提は `inspect` で確認する。reader、Kernel、使用する OCaml コンパイラ・実行系は検査結果の信頼に関与する。通常の OCaml 実装そのものの形式的な健全性証明は未実施。独立した Rocq 実装の保証は第9節に記載する。

自然数・算術・論理の規則は、Kernel に組み込まず、[証明ライブラリ](../examples/commons/README.md)のシグネチャとして与える。演算の再帰方程式や述語の導入・除去規則も明示した前提であり、定数の展開や計算規則を追加するものではない。収録した定理と前提の説明は[証明カタログ](proofs.md)を参照する。

## 5. tp言語 (.tp)

```ebnf
program = { import | declaration } ;
import = "import", path, ";" ;
path = '"', path_character, { path_character }, '"' ;
declaration
  = "axiom", name, { parameter }, ":", term, ";"
  | ("def" | "theorem"), name, { parameter },
    ":", term, ":=", term, ";" ;
parameter = "(", name, { name }, ":", term, ")" ;
term
  = "forall", parameter, { parameter }, ",", term
  | "fun", parameter, { parameter }, "=>", term
  | arrow ;
arrow = application, [ "->", term ] ;
application = atom, { atom } ;
atom = name | "Type" | "Kind" | "(", term, ")" ;
```

識別子は ASCII の `[A-Za-z_][A-Za-z0-9_']*`。`axiom def theorem import forall fun Type Kind` は予約語。`//` から行末はコメント。数値リテラルや中置算術演算はない。

`import "../examples/commons/nat/addition.tp";` は、指定ファイルの宣言をその位置に読み込む。相対パスは読み込み元の実体ファイルのディレクトリを基準とし、絶対パスも許す。パスは空でない二重引用符付きの文字列で、引用符・改行・バックスラッシュを含められない。エスケープ構文はない。

読み込みは宣言順の深さ優先。同じ実体ファイルは `realpath` で識別し、1回のコンパイルにつき1度だけ読み込む。`./`、`../`、シンボリックリンクによる別表記も同じファイルとして扱う。循環 import と存在しないファイルはエラー。import 先の構文・名前解決エラーは、そのファイル名と行・列を表示する。

名前空間・別名・選択的 import はない。読み込んだ宣言は同じグローバルシグネチャに入り、別ファイルの同名宣言も拒否する。import より後の宣言を先に参照することはできない。コンパイル済み記号列は依存する宣言をすべて含むため、検証時に元の `.tp` ファイルや import の解決は不要。

適用は左結合、矢印は右結合。適用の方が矢印より強く結合する。`forall` と `fun` を適用の引数に置く場合は括弧を使う。

名前解決は最も内側のローカル変数を優先し、次に先行するグローバル宣言を探す。ローカルのシャドーイングは許す。グローバルの重複、前方参照、自己参照は拒否する。`_` も通常の名前であり、穴ではない。

`(x y : A)` は `(x : A) (y : A)` という逐次束縛へ展開する。この規則はシャドーイングがある場合にも適用する。

| 表記 | 展開 |
| --- | --- |
| `f x y` | `App(App(f,x),y)` |
| `A -> B` | 名前のない binder を持つ `Pi(A,B)` |
| `forall (x:A), B` | `Pi(A,B)` |
| `fun (x:A) => b` | `Lam(A,b)` |
| 宣言の引数 | 型には Π、本体には λ を外側から追加 |
| `axiom name : A;` | `encode(A)` の後に `:` |
| `def/theorem name : A := t;` | `encode(A) encode(t) !` |

匿名の矢印 binder も de Bruijn の深さに数える。型と本体はそれぞれの束縛構造に従って名前解決する。

`def` と `theorem` の意味は同じ。いずれも検査後は不透明。たとえば `id a` と `a` は定義的に等しくならない。インラインの `(fun (x:A) => x) a` は β 簡約で `a` と等しくなる。

## 6. CLI と資源制限

```text
compile SOURCE [-o FILE] [--sourcemap FILE] [--fuel N]
check ASSEMBLY [--prelude FILE] [--no-axioms] [--fuel N]
inspect ASSEMBLY [--fuel N]
```

`compile` は指定した入口ファイルと、その推移的な import を空のシグネチャからコンパイルし、生成した記号列全体を検査してから出力する。すべての読み込み・検査が成功するまで出力先を書き換えない。ソース prelude の別出力は未対応。表示名は出力形式には含まれない。

`compile --sourcemap FILE` は宣言単位の JSON 対応表を別ファイルに保存する。`-o` を省いた標準出力との併用も可能。記号列と対応表に同じ出力先は指定できない。読み込み・型検査の失敗時には、どちらの出力先も書き換えない。出力時の I/O エラーに対する2ファイルの同時更新は保証しない。

形式は `{"version":1,"mappings":[...]}`。これは tinyprover 独自の形式であり、JavaScript の Source Map v3 ではない。各要素は次のフィールドを持つ。

| フィールド | 意味 |
| --- | --- |
| `constant` | 登録順の定数番号（0始まり） |
| `name` | 元の宣言名 |
| `file` | ファイル読み込み API では canonical な絶対パス。`Source.compile` では `null`。位置付き解析や Web API では指定したパス |
| `line`, `column` | 宣言キーワードの行・バイト列（1始まり。タブは1列） |
| `start_byte`, `end_byte` | 出力記号列の0始まりの半開区間。登録命令を含み、末尾改行を除く |

import 展開後の登録順で1宣言につき1要素を記録する。空の入力では配列も空。バイト範囲は生成した記号列そのものに対応するため、改行を削除するなどの編集後には使えない。対応表は検証には使用せず、CLI の `check` / `inspect` の診断形式も変更しない（Webデモ等での補助的な名前表示に利用される）。

`check --prelude FILE` は同じ Kernel に prelude を読み込み、その後、対象ファイルを前提追加禁止で読む。番号は prelude から続く。`--no-axioms` も対象ファイルの前提追加を禁止する。

`check` と `inspect` は、いずれも再検証後に登録順の全定数を `cN [assumption|proven] : 型` として表示し、最後に宣言数と前提数を報告する。prelude を指定した `check` は prelude の定数も表示する。各定数の型は括弧付きの名前表現で表示し、ローカル名には入力の識別子と衝突しない `$x0` などを使用する。これは表示用であり、上位言語のソースではない。`inspect` に `--prelude` / `--no-axioms` は指定できない。

import した宣言も含め、既定の fuel は実行全体で 1,000,000。正の OCaml `int` を指定できる。推論と弱頭正規化の呼び出しで消費する。尽きたら検証失敗とする。資源不足を証明成功や型の一致として扱わない。prelude と本体では同じ budget を使う。

fuel は時間・メモリの完全な上限ではない。構文解析、shift、置換、構造比較にも資源を使う。極端に深い入力での `Stack_overflow` は CLI で失敗として処理する。敵対的入力に対するプロセス隔離やハードなメモリ制限は本実装の範囲外。

終了コードは成功0、入力・検証・I/O・資源エラー1、CLI の使い方のエラー2。記号言語の診断は0始まりの byte offset、ソース構文・名前解決の診断は1始まりの行・列。ソースの型エラーはコンパイル後の記号列上の位置に加えて、対応する元の宣言の行・列・名前を報告する。ファイル全体で失敗した場合、成功した検証結果として扱わない。埋め込み API ではエラー以前の登録は残るため、ファイル単位の原子性が必要なら新しい Kernel を使う。

`--fuel` の整数変換失敗・非正値、および記号列と対応表の出力先の同一性は、現在の実装ではエラー1として扱う。未知のコマンド・オプション、引数不足、コマンドに使えないオプションはエラー2。

## 7. OCaml API

ライブラリは `tinyprover_core`、`tinyprover_pa`、`tinyprover_tp` に分かれる。pa は core に、tp は core と pa に依存する。ファイル import に必要な `unix` は tp の依存とする。

| API | 動作 |
| --- | --- |
| `Tinyprover_core.Term` | 7種類の AST、`shift`、`instantiate`、`pretty` |
| `Tinyprover_core.Kernel.create ?fuel ()` | 空のシグネチャと独立した fuel を作る。非正値は `Invalid_argument` |
| `Kernel.infer k t` | 空の文脈で型を推論する。定数を登録しない |
| `Kernel.assume k A` / `Kernel.prove k A t` | 検査後に定数を追加し、定数番号を返す |
| `Kernel.entries k` | 登録順の型と由来を返す |
| `Tinyprover_pa.Reader.run ?allow_axioms k source` | 記号列を読み、指定 Kernel に登録する。前提追加は既定で許す |
| `Tinyprover_pa.Writer.encode t` | 項を記号列に符号化する。型検査や登録命令の追加は行わない |
| `Tinyprover_tp.Source.parse` / `Source.compile` | 文字列を解析／検査付きコンパイルする。import は拒否する |
| `Source.parse_items ?file` | import と宣言を区別して解析し、任意のファイル位置を付ける |
| `Source.load path` / `Source.compile_file ?fuel path` | import を展開した宣言一覧／検査済みコンパイル結果を返す |
| `Source.compile_declarations ?fuel ds` | 宣言一覧を符号化し、新しい Kernel で記号列を再検査する |
| `Source.sourcemap_json result` | 第6節の対応表を JSON にする |
| `Source.annotate_assembly_error mappings message` | 対応するバイト範囲の診断に元位置と宣言名を添える。範囲外は変更しない |

`Kernel.t` は抽象型とし、未検査の定数を直接追加する API は公開しない。`Source.compiled` は `assembly`、登録順の `names`、import 展開済みの `declarations`、`sourcemap` を持つ。生成した記号列の再検査に失敗した場合、コンパイル結果は返さない。

`Source.parse_items_with` / `parse_with` / `load_with` は AST の構築方法を `syntax` レコードで受け取る。通常 API は `default_syntax` を使う。解析と名前解決・型検査は別の操作であり、解析の成功だけでは証明の受理を意味しない。

## 8. Web デモ

`web/` のデモは、通常のコンパイラと Kernel を js_of_ocaml で JavaScript に変換して実行する。ビルドは `dune build @web/browser`。配信物は `index.html`、`app.js`、`browser.bc.js`、`catalog.json` で、証明例のソースは JavaScript に同梱する。カタログは配信元から読み込むが、入力したソースと記号列のコンパイル・検査はブラウザ内で行う。

画面は tp ソース、pa 記号列、検査結果の3ペインを持つ。コンパイル成功時は pa を更新して検査し、失敗時は pa を空にして診断を表示する。ソースまたは pa の編集時は対応表と検査結果を無効化し、再コンパイル／再検査が必要であることを表示する。

カタログの分類・定理名から証明例を選択できる。tp の証明例はビルド時に import を宣言位置へ展開し、共通依存を重複排除した単一ソースにする。pa の例はそのまま検査する。入力中の import はファイルシステムを使えないため拒否する。

`globalThis.tinyprover` に次の API を公開する。

| API | 動作 |
| --- | --- |
| `examples` | `{path, source}` の配列を表す JSON 文字列 |
| `compileAt(path, source)` | 表示用パス付きでコンパイルし、記号列と対応表を返す |
| `compile(source)` | 文字列をコンパイルし、記号列を返す |
| `checkMapped(source)` | 直近の成功した `compileAt` の出力と完全一致する場合に宣言名・元位置を使って再検査する |
| `check(source)` | 対応表を使わず再検査する |

関数の返り値は `{ok: boolean, output: string}`。成功した `compileAt` は `sourcemap` に JSON 文字列も返す。`compileAt` は呼び出し時に前回の対応表を破棄し、成功した場合だけ保存する。`checkMapped` は改行を含む1バイトでも違えば通常の `cN` 表示へ戻る。検査ごとに新しい Kernel を作り、既定 fuel は 1,000,000。Web API から fuel や prelude、公理禁止を指定する機能はない。

検査 API は全定数の型・由来・宣言数・前提数を返す。画面の成功表示は、その結果から `proven` の宣言を抽出した「宣言名: 検査成功」とし、証明済み宣言がなければ「検査成功」と表示する。失敗時は診断を表示する。この表示の違いは検査規則を変更しない。

## 9. Rocq 実装と形式証明

`rocq/` は通常の OCaml 実装と独立した定義・証明・抽出実装を含む。通常の Dune ビルドに Rocq は不要。`make -C rocq verify` は各開発の証明コンパイルと `rocq check`、`make -C rocq test` は抽出実装・生成物の実行テストも行う。構成と実行方法は [Rocq の README](../rocq/README.md)を参照する。

### 9.1 pa 検査器（rocq4pa）

`rocq/pa/Checker.v` の検査器を OCaml に抽出する。既存の `Tinyprover_core.Kernel` は呼ばない。整形式のシグネチャについて、`check_program_sound` は受理した宣言列の宣言的な妥当性を、`declarative_program_complete` は公理ポリシーを満たす妥当な宣言列が十分な fuel で受理されることを保証する。`program_correct` は両者の同値性を表す。型保存・合流性・型付き項の強正規化も Rocq 内で証明している。

```text
rocq4pa check FILE [--prelude FILE] [--no-axioms] [--fuel N]
```

prelude を空のシグネチャから検査し、本体では新しい前提を禁止する。型エラー・公理禁止・fuel 不足は共通の検査失敗として報告する。字句・スタックエラーにはバイト位置を付ける。手書きの pa パーサー、I/O、CLI と Rocq 内の AST の対応は未検証。[保証と制限](../rocq/pa/README.md)を参照する。

### 9.2 tp 変換器（rocq4tp）

`.tp` の字句解析・構文解析・有限ファイル集合上の import 展開、糖衣展開、名前解決、宣言変換、pa codec を Rocq で実装し、抽出コードを CLI で使用する。ファイル I/O、`realpath`、依存表の収集は OCaml が担当する。

糖衣を保持した AST からの展開、独立した翻訳仕様に対する名前解決・宣言変換の健全性・完全性、宣言名・種類・数・スコープの保存を証明している。`pa_roundtrip` は宣言列の符号化・復号の往復性を保証する。`compile_surface_pa_sound` / `compile_surface_pa_complete` は糖衣 AST から pa 出力までの保証、`compile_surface_pa_recheck` は同じ fuel と公理ポリシーで出力を再検査できることを保証する。

```text
rocq4tp check SOURCE.tp [--no-axioms] [--fuel N]
rocq4tp compile SOURCE.tp [-o OUTPUT.pa] [--no-axioms] [--fuel N]
rocq4tp check-pa INPUT.pa [--no-axioms] [--fuel N]
```

`compile` は空白なしの pa を出力し、`check-pa` は抽出した復号器と検査器を使う。`--no-axioms` は import 先も含むすべての前提を禁止する。prelude と sourcemap は未対応。構文エラーはファイル名付きで、行・列は保持しない。入力・名前解決・型付け・公理ポリシー・fuel 不足による検査拒否は共通の診断となる。読み込み・解析失敗は別途報告する。検査前の失敗では出力先を変更しないが、書き込み中の I/O 障害に対する原子的更新は保証しない。

lexer/parser と独立した文法との一般的な同値性、import 展開の一般的な正しさは未証明。名前付き言語自身の型付け・置換・α 同値との対応、および既存 OCaml 実装との一般的な同値性も未証明。詳細は [rocq4tp の README](../rocq/tp/README.md)を参照する。

### 9.3 実装ごとの資源制限

| 実装 | fuel の意味・既定値 | CLI の範囲 | pa の index 上限 |
| --- | --- | --- | --- |
| 通常 OCaml | 全検査で共有する消費ステップ数。1,000,000 | 正の OCaml `int` | OCaml `int` |
| rocq4pa | 再帰の深さ。2048 | 1〜100000 | 100000 |
| rocq4tp | 型検査の再帰の深さ。2048 | 1〜100000 | codec は Rocq の自然数を扱い、固定の数値上限を設けない |

Rocq 版の fuel は、通常実装の共有ステップ数とは異なる。rocq4pa の prelude と本体には同じ深さの値を渡し、消費ステップ数を共有する方式は使わない。rocq4tp の解析・import 用の内部 fuel は入力から計算し、型検査の指定値と分ける。

両 Rocq CLI の終了コードは成功0、検査・入力・I/O・資源エラー1、使用法エラー2。十分な fuel の定理は Rocq の自然数を対象とし、CLI 上限や実機の時間・メモリ内での成功を保証しない。一度の拒否は fuel 不足でも起きるため、型誤りの証明にはならない。

### 9.4 固定理論の符号化

| 開発 | 証明した範囲 |
| --- | --- |
| [命題論理 NK・LK](../rocq/calculi/README.md) | 固定シグネチャ上で、独立した NK・LK 導出の存在と任意の閉じた LF 証明項の存在、AST 検査器に受理される項の存在が同値。LK のカット除去・cut の許容性も証明 |
| [ZFC](../rocq/zfc/README.md) | 固定シグネチャと閉じた式について、独立した `ZFC_proves` と AST 検査器に受理される pa 証明項の存在の同値性を `ZFC_pa_iff` で証明。全理論の prelude と具体的な証明項も再検査 |

NK・LK の対応は結合版の固定 prelude のみをシグネチャとする。任意の追加公理・不透明な定理定数を含むシグネチャへの一般化、実行可能な導出復元器やカット除去器は提供しない。ZFC の意味論的健全性は古典論理と全 ZFC 公理を満たす解釈を明示的な前提とする。モデルの存在や公理の無矛盾性を証明したものではない。これらの開発の出力バイト列と Rocq 内の AST の一般的な対応は未証明。

以上の主要な保証には追加の Rocq 公理や `Admitted` を使わない。Rocq のカーネル・抽出機構、OCaml コンパイラ・実行系、I/O は信頼境界に残る。Rocq の定理は通常の OCaml コンパイラ・Kernel 自体の形式検証を代替しない。
