# pa 形式検証

tinyprover の `.pa` を独立に再検査する、Rocq で実装・証明した型検査器です。
Gallina の復号器と検査器を OCaml に抽出し、専用 CLI から実行します（既存の OCaml カーネルは呼び出しません）。

## ビルドと実行

抽出 CLI のビルドには ocamlfind と Zarith が必要です。

```sh
# 検証とテスト
make -C rocq/pa
make -C rocq/pa test

# 抽出した CLI の実行
rocq/pa/_build/pa check examples/identity.pa
rocq/pa/_build/pa check /tmp/proof.pa --prelude /tmp/prelude.pa
```

## 証明した保証

宣言的な型付け規則（`typing` / `valid_program`）に対し、検査器（`check_program`）の以下を証明しています（追加公理や `Admitted` は使用していません）。

- **健全性（Soundness）**: 検査器が受理した宣言列は、宣言的な型付け規則を満たす。
- **完全性（Completeness）**: 正しい宣言列は、十分な fuel を与えれば必ず受理される。
- **型理論の基本性質**: 型保存（subject reduction）、合流性（confluence）、型付き項の強正規化（strong normalization）。
- **Codec の正しさ**: 任意バイト列の復号と、独立した字句・スタック仕様の同値性。

## 信頼境界と制限

- **公理の無矛盾性**: 登録された公理自体の無矛盾性は保証しません。
- **計算資源**: fuel は再帰の深さであり、実機の時間・メモリ内での完了を保証するものではありません。
- **実行基盤**: Rocq の抽出機構、自然数を多倍長整数に置き換える抽出設定、Zarith、OCaml コンパイラ・実行系、ファイル I/O は信頼境界に残ります。

## TODO

- [ ] 別の LF 定式化との同値性の証明
- [ ] 既存 OCaml 実装の shift・置換処理との同値性の証明
- [ ] CLI の I/O および引数処理の形式検証
