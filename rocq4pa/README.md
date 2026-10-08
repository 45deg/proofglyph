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

# Rocq 内の証明、抽出した CLI と既存実装の照合
make -C rocq4pa test
dune runtest
```

Rocq が別の環境にある場合は `make -C rocq4pa ROCQ=/path/to/bin/rocq` と指定できます。
`OCAMLC` も上書き可能です。生成ファイルはすべて `rocq4pa/_build/` に置きます。
`make verify` は証明のコンパイル、仮定の確認、`rocq check` による再検査まで実行します。

Rocq 9.2.0 / Stdlib 9.1.0、抽出先 OCaml 5.5.0 で検証しています。
CLI テストは正例・反例22件、決定的な変異入力120件、資源制限・prelude の検査、
既存の `.tp` 全48件（フェルマーの小定理を含む）の再検査を行います。

## 証明した保証

CLI が使う検査器は `Checker.v` の `check_program` です。
宣言的な型付け規則（declarative typing rules）`typing` / `valid_program` に対して、健全性と
十分な fuel による完全性を証明しています。追加公理・`Admitted` は使っていません。

```text
check_program_sound:
  wf_signature Σ →
  check_program fuel allow Σ ds = Some Σ' → valid_program Σ ds Σ'

declarative_program_complete:
  wf_signature Σ → permitted_declarations allow ds → valid_program Σ ds Σ' →
  ∃ N, ∀ fuel ≥ N, check_program fuel allow Σ ds = Some Σ'
```

`program_correct` は、ある fuel で受理されることと、許可された宣言列が
宣言的に正しいことの同値性です。`program_monotone` により、受理後に
fuel を増やしても結果は変わりません。型が正しくない入力は、どの fuel でも受理されません。
ただし、一度の拒否は fuel 不足でも起きるため、型誤りの証明にはなりません。

前提は次のとおりです。

- `wf_signature Σ`：空のシグネチャから順に、それ以前のシグネチャでソートが付く型だけを追加したシグネチャ。
- `permitted_declarations allow ds`：`allow = false` なら公理宣言を含まない。
- `valid_program Σ ds Σ'`：各宣言型にソートが付き、証明宣言にはその型を持つ証明項がある。

検査成功、正規化の停止性、有限の検査導出、公理の無矛盾性は前提に含めていません。
型が正しい不透明な公理を許します。シグネチャには型だけを追加し、証明の本体は展開しません。

空のシグネチャは整形式です。`accepted_program_wf` は、受理した宣言列が作るシグネチャも
整形式であることを保証します。CLI は空のシグネチャから始め、prelude も同じ検査器で検査します。
`prelude_and_main_complete` は、有効な prelude と公理禁止の本体について、
共通の十分大きな fuel で両方を受理できることを証明しています。

項単位でも証明しています。

```text
declarative_infer_complete:
  wf_signature Σ → wf_context Σ Γ → typing Σ Γ t A →
  ∃ B N, conv B A ∧ ∀ fuel ≥ N, infer fuel Σ Γ t = Some B

declarative_check_complete:
  wf_signature Σ → sorted_type Σ [] A → typing Σ [] t A →
  ∃ N, ∀ fuel ≥ N, check fuel Σ t A = true
```

`wf_context` は各局所変数の型が、それ以前の文脈で `Type` を持つことを要求します。
検査では目標型 `A` 自身のソートも要求します。推論では `Type : Kind` も扱い、
返す型は宣言的な型と β 同値であることを保証します。

`proper_type Σ Γ A` を満たす型を、ここでは適正な型と呼びます。これは、
ソートを持つ型と `Kind` 自体を含む条件です。`Kind` は型付けできないため、
適正な型であることと、ソートを持つことは区別します。`Regularity.v` は、
型付けの結論に現れる型と β 同値な適正な代表型の存在を証明します。

`Verification.v` は、健全性・完全性・シグネチャの整形式性保存・fuel の単調性について
`Print Assumptions` を実行します。すべて `Closed under the global context` であり、
ビルド時には `rocq check` で再検査します。

## ファイル

| ファイル | 定義・証明 |
| --- | --- |
| `Syntax.v` | 項、shift、置換、β 同値、宣言的型付け |
| `Substitution.v` | 同時置換・変数の付け替えの代数則 |
| `Kernel.v` / `Program.v` | 正規化・同値判定の実装と健全性、宣言的な宣言列仕様 |
| `WellFormed.v` / `TypingSubstitution.v` | 整形式性、弱化、型付き置換、文脈変換 |
| `Evaluation.v` | 有限の導出を持つ評価関係と正規化器の対応、fuel の境界と単調性 |
| `Confluence.v` / `Generation.v` | 合流性、正規形・型の一意性、型付けの反転補題（generation lemma） |
| `Preservation.v` / `Regularity.v` | 型保存（subject reduction）、正則性、カインドの構造 |
| `Normalization.v` | 強正規化から有限の評価導出への接続 |
| `Arity.v` / `Reducibility.v` | 型の形による対応、reducibility による強正規化 |
| `TypedNormalization.v` | 宣言的型付けから強正規化・有限の評価導出への接続 |
| `Checker.v` | 現行検査器、健全性、宣言的完全性、fuel の単調性 |
| `Verification.v` | 最終定理の仮定確認 |
| `Extraction.v` / `main.ml` | OCaml 抽出、手書きパーサーと CLI |

## 信頼境界と制限

- 定理の対象は Rocq 内の AST と宣言列です。手書きのバイトパーサー、I/O、CLI が
  それらを正しく構成することは形式検証していません。
- Rocq のカーネル・抽出機構、OCaml コンパイラと実行系を信頼します。
  抽出コードを手で変更せず、自然数を機械整数に置き換える抽出指示も使いません。
- 任意に追加した公理の無矛盾性、`.tp` から意図した命題への翻訳、
  既存 OCaml カーネルそのものの正しさは保証しません。
- 宣言的仕様は変換先のソートを各変換規則で要求しません。
  別の LF 定式化との同値性、既存 OCaml の shift・置換との同値性は未証明です。
- fuel は再帰の深さです。既存実装の共有ステップ数とは意味が異なり、
  資源不足による拒否が一致するとは限りません。
- 十分な fuel の定理は任意の自然数を対象とします。CLI の既定 fuel は 2048、
  指定範囲は 1〜100000、入力 index も 100000 以下です。
  **必要な fuel が CLI の上限以下であることや、実機の時間・メモリ内での成功は保証しません。**
- 終了コードは成功 0、検査・入力・I/O・資源エラー 1、CLI 使用法エラー 2。
  型エラーと fuel 不足は同じ検査失敗として報告します。
