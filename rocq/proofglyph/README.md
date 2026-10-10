# proofglyph 形式検証

proofglyph の `.pg` を独立に再検査する、Rocq で実装・証明した型検査器です。
Gallina の復号器と検査器を OCaml に抽出し、専用 CLI から実行します（既存の OCaml カーネルは呼び出しません）。

## ビルドと実行

抽出 CLI のビルドには ocamlfind と Zarith が必要です。

```sh
# 検証とテスト
make -C rocq/proofglyph
make -C rocq/proofglyph test

# 抽出した CLI の実行
rocq/proofglyph/_build/proofglyph check examples/identity.pg
rocq/proofglyph/_build/proofglyph check /tmp/proof.pg --prelude /tmp/prelude.pg
```

## 証明した保証

宣言的な型付け規則（`typing` / `valid_program`）に対し、弱頭検査器（`WeakCheckerImpl.check_program`）の以下を証明しています（追加公理や `Admitted` は使用していません）。

- **健全性（Soundness）**: 検査器が受理した宣言列は、宣言的な型付け規則を満たす。
- **完全性（Completeness）**: 正しい宣言列は、十分な fuel を与えれば必ず受理される。
- **型理論の基本性質**: 型保存（subject reduction）、合流性（confluence）、型付き項の強正規化（strong normalization）。
- **Codec の正しさ**: 任意バイト列の復号と、独立した字句・スタック仕様の同値性。

## 弱頭正規化の健全性と完全性

`WeakHeadSpec.v` は、手書き OCaml カーネルで使われていた弱頭正規化と、
弱頭正規形の部分項を再帰的に比較する方式を、fuel なしの帰納的関係として定義します。
`weak_head` は binder 内や引数を簡約せず、`weak_compare` は Π・λ・適用の
部分項を比較します。`weak_infer` は λ の推論型を再検査しない処理も含みます。
これらの有限な導出は、終了した計算を表します。

`WeakHead.v` では、以下を追加公理なしで証明しています。

- `whnf_steps` / `whnf_sound`: 弱頭簡約は β 簡約列であり、β 同値を保つ。
- `whnf_preserves_type`: 弱頭簡約は型を保存する。
- `weak_equal_sound`: 再帰的な比較が成功した項は β 同値である。
- `weak_infer_sound` / `weak_check_sound`: 推論・証明検査の成功は宣言的な型付けを満たす。
- `weak_check_program_sound` / `weak_accepted_program_wf`: 受理した宣言列は正しく、シグネチャの整形式性を保つ。
- `cached_infer_sound` / `inference_cache_insert_valid`: 文脈全体と項をキーとする推論キャッシュは、同じシグネチャ上の成功結果だけを保存すれば健全性を保つ。

`WeakNormalization.v` は、型付き項の強正規化と合流性から、以下を証明します。

- `strongly_normalizing_weak_head`: 強正規化する項は弱頭正規形へ到達する。
- `weak_equal_complete`: 強正規化する β 同値な項の再帰比較は成功する。
- `declarative_weak_infer`: 整形式なシグネチャ・文脈で型付け可能な項は、その型と β 同値な型を弱頭版で推論できる。

`WeakKernelImpl.v` / `WeakCheckerImpl.v` は fuel 付きの実行可能な弱頭検査器です。
`WeakEvaluation.v` は弱頭簡約・比較と帰納的仕様の対応、および十分な fuel での成功と fuel の単調性を証明します。
`WeakChecker.v` は実行可能な推論の仕様との対応、健全性、宣言的完全性、宣言列・prelude の検査の正しさを証明します。
完全性は、ある上限以上のすべての fuel で成功するという保証です。任意の未型付け項の終了性は主張しません。

抽出 CLI は弱頭版を使用します。Hieratic の再検査も同じ弱頭検査器を使います。
完全正規化版の `Checker.v` は比較用に残し、Hieratic の出力を正規化する処理には引き続き `normal` を使います。
`WeakExamples.v` は binder・引数を弱頭簡約しないこと、比較ではその内部も調べること、fuel 枯渇時の拒否を検証します。
`make -C rocq/proofglyph verify` は主要定理の `Print Assumptions` と `rocq check` による再検査を行います。

推論キャッシュはまだ抽出検査器には実装していません。キャッシュの証明はリストによるモデルを対象とし、
ホスト OCaml のハッシュ表、機械整数、手書きコードとモデルの対応は未証明です。

## 信頼境界と制限

- **公理の無矛盾性**: 登録された公理自体の無矛盾性は保証しません。
- **計算資源**: fuel は再帰の深さであり、実機の時間・メモリ内での完了を保証するものではありません。
- **実行基盤**: Rocq の抽出機構、自然数を多倍長整数に置き換える抽出設定、Zarith、OCaml コンパイラ・実行系、ファイル I/O は信頼境界に残ります。

## TODO

- [ ] 別の LF 定式化との同値性の証明
- [ ] 既存 OCaml 実装の shift・置換処理との同値性の証明
- [ ] CLI の I/O および引数処理の形式検証
