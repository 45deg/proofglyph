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
CLI テストは正例・反例22件、決定的な変異入力120件、資源制限・prelude の検査、
既存の `.tp` 全48件（フェルマーの小定理を含む）の再検査を行います。

## 証明した保証

CLI が使う検査器は `DirectKernel.v` の `check_program_direct` です。
宣言的な型付け規則 `typing` / `valid_program` に対して、健全性と
十分な fuel による完全性を証明しています。追加公理・`Admitted` は使っていません。

```text
check_program_direct_sound:
  wf_signature Σ →
  check_program_direct fuel allow Σ ds = Some Σ' → valid_program Σ ds Σ'

declarative_program_direct_complete:
  wf_signature Σ → permitted_declarations allow ds → valid_program Σ ds Σ' →
  ∃ N, ∀ fuel ≥ N, check_program_direct fuel allow Σ ds = Some Σ'
```

`program_direct_correct` は、ある fuel で受理されることと、許可された宣言列が
宣言的に正しいことの同値性です。`program_direct_monotone` により、受理後に
fuel を増やしても結果は変わりません。型が正しくない入力は、どの fuel でも受理されません。
ただし、一度の拒否は fuel 不足でも起きるため、型誤りの証明にはなりません。

前提は次のとおりです。

- `wf_signature Σ`：空の署名から順に、それ以前の署名で sort が付く型だけを追加した署名。
- `permitted_declarations allow ds`：`allow = false` なら公理宣言を含まない。
- `valid_program Σ ds Σ'`：各宣言型に sort が付き、証明宣言にはその型を持つ証明項がある。

検査成功、正規化の停止性、有限の検査導出、公理の無矛盾性は前提に含めていません。
型が正しい不透明な公理を許します。署名には型だけを追加し、証明の本体は展開しません。

空の署名は整形式です。`accepted_direct_program_wf` は、受理した宣言列が作る署名も
整形式であることを保証します。CLI は空の署名から始め、prelude も同じ検査器で検査します。
`prelude_and_main_direct_complete` は、有効な prelude と公理禁止の本体について、
共通の十分大きな fuel で両方を受理できることを証明しています。

項単位でも証明しています。

```text
declarative_infer_direct_complete:
  wf_signature Σ → wf_context Σ Γ → typing Σ Γ t A →
  ∃ B N, conv B A ∧ ∀ fuel ≥ N, infer_direct fuel Σ Γ t = Some B

declarative_check_direct_complete:
  wf_signature Σ → sorted_type Σ [] A → typing Σ [] t A →
  ∃ N, ∀ fuel ≥ N, check_direct fuel Σ t A = true
```

`wf_context` は各局所変数の型が、それ以前の文脈で `Type` を持つことを要求します。
検査では目標型 `A` 自身の sort も要求します。推論では `Type : Kind` も扱い、
返す型は宣言的な型と β 同値であることを保証します。

## 完全性までの証明

`typing` は生の β 同値による変換規則を持ちます。検査器の成功を型付け規則にはしていません。
変換先そのものが未整形式な場合もあるため、正則性は β 同値な整形式の代表の存在として証明します。

1. 同時置換・弱化・型付き置換、β 簡約の合流性、型保存、正則性を証明します。
2. 型の形 `type_shape` が、型レベルの項に対する置換と β 同値で保たれることを示し、
   宣言的な型付けを単純型の arity に対応させます。
3. reducibility の議論から、その arity を持つ項の強正規化を証明します。
   型注釈と束縛子の内部も簡約対象です。
4. `typing_strong_normalization` と `typing_normal_complete` により、整形式な署名・文脈で
   型が付く項は強正規化し、現在の正規化器が十分な fuel で成功すると示します。
5. `declarative_synthesizes_direct` で、宣言的型付けから有限の検査導出を構成します。
   各部分の fuel 境界の最大値を取り、全体の「すべての fuel ≥ N」での成功を得ます。

中心となる定理の `Print Assumptions` はすべて `Closed under the global context` です。
ビルド時に `rocq check` で証明を再検査します。

## λ の検査変更と旧実装

初期実装の `Kernel.v` / `Program.v` は比較用に残しています。旧 `infer` は λ の本体の型を
推論した後、生成した Π 型を再度 `infer` していました。現在の `infer_direct` は、
本体の推論結果が `Kind` なら拒否し、それ以外なら Π 型を返します。

これを正当化するのが `infer_direct_sound` です。整形式な署名・文脈の下では、
推論結果は「`Kind` または sort が付く型」であることを、型付けと同時に証明します。
したがって `Kind` を除けば Π 型の形成条件が成立し、再検査は不要です。
新実装の健全性は整形式な環境を前提にするため、未検査の署名を直接渡す用途は保証外です。
CLI の経路では空の署名と整形式性保存の定理がこの前提を満たします。

今回の宣言的完全性は、この変更を行った **新実装** の定理です。
旧実装について `Completeness.v` に残る `declarative_bridge` などは、引き続き未証明の命題定義です。
旧実装の完全性を証明済みと扱ったり、その命題を公理として使ったりはしていません。
旧実装・既存 OCaml カーネルとの全入力での同値性も主張していません。

`Counterexamples.v` には、整形式でない初期署名や未整形式な目標型を許した場合の、
旧実装への完全性の反例を残しています。`bad_signature_not_wf` などが、それらを
通常の宣言列から構築できないことを示しています。

## ファイル

| ファイル | 定義・証明 |
| --- | --- |
| `Syntax.v` | 項、shift、置換、β 同値、宣言的型付け |
| `Substitution.v` | 同時置換・変数の付け替えの代数則 |
| `Kernel.v` / `Program.v` | 共通の正規化器・宣言仕様、旧検査器とその健全性 |
| `WellFormed.v` / `TypingSubstitution.v` | 整形式性、弱化、型付き置換、文脈変換 |
| `Completeness.v` | 評価導出、fuel の境界、旧検査器の有限導出に対する完全性 |
| `Confluence.v` / `Generation.v` | 合流性、正規形・型の一意性、生成補題 |
| `Preservation.v` / `Regularity.v` | 型保存、正則性、kind の構造 |
| `Normalization.v` | 強正規化から有限評価・十分な fuel への接続 |
| `Arity.v` / `Reducibility.v` | 型の形による対応、reducibility による強正規化 |
| `TypedNormalization.v` | 宣言的型付けから強正規化・正規化成功・同値判定の完全性 |
| `DirectKernel.v` | 現行検査器、健全性、宣言的完全性、fuel の単調性 |
| `Counterexamples.v` / `Tests.v` | 反例、計算例、定理の適用例、仮定表示 |
| `Extraction.v` / `main.ml` | OCaml 抽出、手書きパーサーと CLI |

## 信頼境界と制限

- 定理の対象は Rocq 内の AST と宣言列です。手書きのバイトパーサー、I/O、CLI が
  それらを正しく構成することは形式検証していません。
- Rocq のカーネル・抽出機構、OCaml コンパイラと実行系を信頼します。
  抽出コードを手で変更せず、自然数を機械整数に置き換える抽出指示も使いません。
- 任意に追加した公理の無矛盾性、`.tp` から意図した命題への翻訳、
  既存 OCaml カーネルそのものの正しさは保証しません。
- 今回の宣言的仕様は変換先の sort を各変換規則で要求しません。
  別の LF 定式化との同値性、既存 OCaml の shift・置換との同値性は未証明です。
- fuel は再帰の深さです。既存実装の共有ステップ数とは意味が異なり、
  資源不足による拒否が一致するとは限りません。
- 十分な fuel の定理は任意の自然数を対象とします。CLI の既定 fuel は 2048、
  指定範囲は 1〜100000、入力 index も 100000 以下です。
  **必要な fuel が CLI の上限以下であることや、実機の時間・メモリ内での成功は保証しません。**
- 終了コードは成功 0、検査・入力・I/O・資源エラー 1、CLI 使用法エラー 2。
  型エラーと fuel 不足は同じ検査失敗として報告します。
