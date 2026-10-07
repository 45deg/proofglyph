# rocq4pa

tinyprover の `.pa` を独立に再検査する、Rocq で実装・証明した型検査器です。
Gallina の検査器を OCaml に抽出し、専用 CLI から実行します。既存の
`Tinyprover_core.Kernel` は呼び出しません。

## ビルドと実行

Rocq とその標準ライブラリ、OCaml、Make が必要です。親プロジェクトの
通常の `dune build` / `dune runtest` に Rocq の依存は追加していません。
Rocq の導入は [公式手順](https://rocq-prover.org/docs/using-opam) を参照してください。

```sh
make -C rocq4pa
rocq4pa/_build/rocq4pa check examples/identity.pa

dune exec bin/main.exe -- compile examples/fermat_application.tp -o /tmp/fermat.pa
rocq4pa/_build/rocq4pa check /tmp/fermat.pa

# prelude の後では新しい公理を禁止
rocq4pa/_build/rocq4pa check /tmp/proof.pa --prelude /tmp/prelude.pa
rocq4pa/_build/rocq4pa check /tmp/proof.pa --no-axioms

# Rocq 内の計算例・証明、抽出した CLI と既存実装の照合
make -C rocq4pa test
dune runtest
```

Rocq が別の環境にある場合は `make -C rocq4pa ROCQ=/path/to/bin/rocq` と指定できます。
`OCAMLC` も上書き可能です。生成ファイルはすべて `rocq4pa/_build/` に置きます。
`make verify` は証明のコンパイル、計算例、`rocq check` による再検査まで実行します。

Rocq 9.2.0 / Stdlib 9.1.0、抽出先 OCaml 5.5.0 で検証しています。
CLI テストは正例・反例20件、決定的な変異入力120件、資源制限・prelude の検査、
既存の `.tp` 全48件（フェルマーの小定理を含む）の再検査を行います。

## 証明の対象

| ファイル | 定義・証明 |
| --- | --- |
| `Syntax.v` | 項、shift、捕獲を避ける置換、β 同値、宣言的型付け関係 `typing` |
| `Substitution.v` | 同時置換・変数の付け替えの代数則、既存の shift / instantiate との対応、β 同値の保存 |
| `Kernel.v` | fuel 付き正規化・型推論・型検査と健全性 |
| `Program.v` | 公理・証明の登録、宣言列の検査と健全性、公理禁止の保存 |
| `WellFormed.v` | 署名・文脈・宣言型の整形式性、検査による署名の整形式性保存 |
| `TypingSubstitution.v` | 閉じた署名、弱化、型付き同時置換、一変数の置換、文脈変換 |
| `Completeness.v` | fuel の単調性、有限の検査導出に対する十分な fuel の存在 |
| `Confluence.v` | 並列 β 簡約の合流性、正規形の一意性、Π 型の同値性の分解 |
| `Generation.v` | 宣言的型付けの生成補題、β 同値を除いた型の一意性 |
| `Preservation.v` | β 簡約・複数ステップ・成功した正規化の型保存 |
| `Regularity.v` | 署名・文脈からの型取得の妥当性、型の整形式な代表の存在 |
| `Counterexamples.v` | 前提を付けない宣言的完全性への反例 |
| `Tests.v` | 受理・拒否・依存型・β 同値・置換の計算例、証明の仮定表示 |
| `Extraction.v` | OCaml への抽出。自然数は帰納的表現を保持 |
| `main.ml` | 手書きの `.pa` パーサー、ファイル読み込み、CLI |

中心となる定理は次です。

```text
normal_sound:
  normal fuel t = Some u → conv t u

infer_sound:
  infer fuel Σ Γ t = Some A → typing Σ Γ t A

check_sound:
  check fuel Σ t A = true →
  typing Σ [] t A ∧ ∃ s, typing Σ [] A s ∧ is_sort s

check_program_sound:
  check_program fuel allow Σ ds = Some Σ' → valid_program Σ ds Σ'

no_axioms:
  check_program fuel false Σ ds = Some Σ' → ds に Assume がない
```

`valid_program` は、各宣言がそれ以前の署名だけを用いて正当化されることを表します。
証明宣言には証明項の型付け、公理宣言にも宣言型の sort 検査を要求します。
署名には型だけを追加し、定数の本体を展開しません。

`typing` は生の β 同値による型変換を持つ宣言的な型付け関係です。
検査器の成功自体を型付け規則にしてはいません。変換規則は変換先の型の sort
を前提に取らない形式を採用しています。sort の妥当性を各変換規則に要求する
別の LF 定式化との同値性と強正規化は未証明です。型付き置換と型保存は証明済みです。
正則性は「任意の変換先も整形式」とはせず、β 同値な整形式の代表が存在する形で証明しています。
shift と置換はこの仕様の定義そのものであり、既存 OCaml 関数との同値性も未証明です。

## 十分な fuel と完全性

`Completeness.v` では、成功した検査は fuel を増やしても同じ結果になることを証明しています。
正規化、同値判定、sort 判定、型推論、型検査、宣言・宣言列の検査が対象です。

また、fuel を含まない帰納的な関係を定義しています。
`evaluates` は現在の正規化戦略による有限の評価導出、`synthesizes` / `checks` は
その評価を使う有限の検査導出、`program_derivation` は宣言列の有限の検査導出です。
これらの定義は実装の成功や fuel の存在を前提にしていません。

```text
normal_complete:
  evaluates t u → ∃ N, ∀ fuel ≥ N, normal fuel t = Some u

infer_complete:
  synthesizes Σ Γ t A → ∃ N, ∀ fuel ≥ N, infer fuel Σ Γ t = Some A

check_complete:
  checks Σ t A → ∃ N, ∀ fuel ≥ N, check fuel Σ t A = true

program_complete:
  program_derivation allow Σ ds Σ' →
  ∃ N, ∀ fuel ≥ N, check_program fuel allow Σ ds = Some Σ'
```

境界値は各有限導出の帰納法で構成し、子の境界値の最大値で fuel を共通化します。
`normalization_iff` では `evaluates t u` と、ある fuel で正規化が成功することの同値性も
証明しています。恒等関数の例では、有限の検査導出を構成して `program_complete` を適用しています。

**これは宣言的な `typing` / `valid_program` 全体に対する完全性の証明ではありません。**
そこから有限の検査導出が得られることが、まだ必要です。
整形式な初期署名の下での未解決の目標を `declarative_bridge` として明記しています。
これは命題の定義であり、公理や証明済み定理ではありません。

```text
declarative_bridge（未証明）:
  ∀ allow Σ ds Σ',
    wf_signature Σ → permitted_declarations allow ds →
    valid_program Σ ds Σ' → program_derivation allow Σ ds Σ'
```

`wf_signature` は、空の署名から順に、それ以前の署名で sort が付く型だけを追加した署名です。
`wf_context` は、各局所変数の型がそれ以前の文脈で `Type` を持つことを要求します。
どちらも検査器の成功・停止性・正規化可能性を前提にはしていません。
`permitted_declarations` は `allow = false` のときに公理宣言がないという実行上の方針です。
`valid_program` は、各宣言型の sort と、証明宣言の証明項の型付けを既に要求しています。

項単位の目標も明示しています。

```text
declarative_check_completeness（未証明）:
  wf_signature Σ → sorted_type Σ [] A → typing Σ [] t A →
  ∃ N, ∀ fuel ≥ N, check fuel Σ t A = true

declarative_infer_completeness（未証明）:
  wf_signature Σ → wf_context Σ Γ → typing Σ Γ t A →
  ∃ B N, conv B A ∧ ∀ fuel ≥ N, infer fuel Σ Γ t = Some B
```

検査では目標型自身の sort を要求します。推論では `Type : Kind` も扱うため、
同じ目標型条件は課さず、返す型が `A` と β 同値であることを要求します。

`declarative_complete_if_bridge` は、この命題を仮定すれば目的の完全性が得られることだけを
証明しています。橋渡しには、整形式な署名・文脈でのメタ理論、正規化と β 同値判定の
完全性、型推論との対応を扱う必要があります。

この橋渡しのために、次のメタ理論までは証明済みです。

- `instantiate_as_substitute` / `substitute_beta`：実装で使う置換と同時置換の対応、β 簡約と置換の交換。
- `conv_substitute`：β 同値が置換で保存される。
- `parallel_diamond` / `steps_confluent` / `conv_joins`：並列簡約のダイヤモンド性、複数ステップの合流性、β 同値な項の共通簡約先。
- `normal_forms_unique`：β 同値な正規形は構文的に等しい。
- `conv_pi_injective`：β 同値な Π 型のドメイン同士・本体同士は β 同値。
- `typing_generation` / `typing_unique`：導出から項の構文に対応する規則の前提を取り出せ、同じ項の型は β 同値を除いて一意。
- `typing_subject_closed` / `wf_signature_closed`：型付けされた項は局所文脈に収まり、整形式な署名の宣言型は自由な局所変数を含まない。
- `typing_rename` / `typing_weaken` / `typing_substitute` / `typing_instantiate`：文脈に合う変数の付け替え、弱化、型付き同時置換、一変数の置換で型付けが保存される。
- `typing_context_conversion`：対応する宣言型が β 同値な文脈に移しても型付けが保たれる。
- `subject_reduction` / `normalization_preserves_type`：型注釈・束縛子の内部も含む β 簡約、および成功した正規化が型を保つ。
- `typing_regular_representative`：整形式な署名・文脈の下で `t : A` なら、`A` と β 同値な型 `B` が存在し、`B = Kind` または `B` 自身に sort が付く。

これらは正規化の停止性を仮定しません。`equal_complete_from_convertibility` では、
β 同値な二つの項の評価導出が与えられれば、十分な fuel で `equal` が成功することも示しています。
ただし、**型が付くことから評価導出の存在を得る証明はまだありません**。
正規化の停止性と、宣言的導出から `synthesizes` を構成する部分が残ります。
`conv_substitute` は β 同値の保存、`typing_substitute` は型付けの保存で、別の定理です。
`typing_regular_representative` は元の型 `A` 自身の整形式性を主張しません。
生の `ty_conv` が未整形式な変換先を許すことは、既存の反例と矛盾せずに扱っています。

前提を付けずに任意の署名へ拡張した完全性は偽です。`Counterexamples.v` には次を証明しています。

- 変換先の型が整形式でない場合、`typing [] [] t A` だけでは `check` は成功しません。
- 不正な初期署名では、宣言型に sort が付く `valid_declaration` でも全 fuel で拒否されます。
  反例は、β 簡約で消える位置に発散項 Ω を置いた関数型です。宣言的な β 同値では消せますが、
  現在の正規化器はその引数を先に評価するため停止しません。

これは通常の `Axiom` / `Admitted` によって矛盾する命題を仮定することとは異なります。
公理でも宣言型の整形式性は必要です（[Rocq の型付け規則](https://rocq-prover.org/doc/V9.1.0/refman/language/cic.html)）。
今回の反例は不正な型を署名へ直接注入したものであり、通常の検査経路のバグを示すものではありません。
従来の完全性の定式化に、整形式性の前提が欠けていました。
完全性の目標には公理の無矛盾性を要求しません。型が正しい不透明な公理は引き続き許します。

`accepted_prelude_wf` により、空の署名から受理した prelude がこの整形式性を満たすことを証明しています。
`valid_program_preserves_wf` は宣言的な有効性についても保存を示します。
`bad_signature_not_wf` / `bad_signature_not_from_accepted_prelude` により、反例の署名が条件を満たさず、
通常の prelude 検査では構築できないことも証明済みです。
`bad_expansion_not_sorted` は最初の反例を目標型の条件が除外することを示します。
これらは追加公理・`Admitted` なしで検査しています。整形式性を明示しても、完全性の橋渡し自体は未証明です。

## 信頼境界と制限

- 健全性定理は Rocq 内の AST と宣言列が対象です。手書きのバイトパーサー、
  I/O、CLI がそれらを正しく構成することは形式検証していません。
- 実行ファイルでは Rocq の抽出機構、OCaml コンパイラと実行系も信頼します。
  抽出したコードを手作業で変更しません。自然数を機械整数に置き換える抽出指示も使いません。
- 任意に追加した公理の無矛盾性や、`.tp` から意図した命題への翻訳は保証しません。
- 既存の OCaml カーネルの形式検証ではありません。既存実装とは回帰例で照合しますが、
  全入力に対する同値性や、健全な型付け関係の意味論的モデルは証明していません。
- fuel は再帰の深さの上限です。既存実装の共有ステップ数とは意味が異なります。
  正規化も関数・引数を先に正規化する方式なので、資源不足による拒否は一致しません。
  有限の検査導出に対する十分な fuel の存在は証明済みですが、宣言的型付け全体の完全性は未証明です。
- CLI の既定 fuel は 2048、指定可能範囲は 1〜100000。入力 index は 100000 以下に
  制限します。既存実装が受け付ける巨大な index は資源制限として拒否する場合があります。
  時間・メモリの厳密な上限ではありません。
  十分な fuel の定理は Rocq 内の任意の自然数が対象です。境界値が CLI の上限以下であることや、
  実機の時間・メモリ内で実行できることは保証しません。
- 終了コードは成功 0、検査・入力・I/O・資源エラー 1、CLI の使用法エラー 2。
  型エラーと fuel 切れは同じ検査失敗として報告します。型検査失敗時に途中の受理結果は表示しません。

次の課題は正規化の停止性と `declarative_bridge` の証明です。パーサーの形式検証も未実施です。
