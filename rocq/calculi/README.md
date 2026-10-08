# 命題論理 NK / LK over pa

古典命題論理の自然演繹（NK）とシーケント計算（LK）を、固定の pa prelude と LF 証明項として符号化した検証です。
NK・LK の導出と tinyprover の証明項の対応関係、および LK のカット除去定理を Rocq で証明しています。

## ビルドと実行

```sh
# 検証とテスト
make -C rocq/calculi test

# pa ファイルの生成と検査
make -C rocq/calculi export
dune exec bin/main.exe -- check rocq/calculi/_build/proofs.pa --prelude rocq/calculi/_build/prelude.pa
```

## 証明した保証

- **導出と証明項の対応（Adequacy）**: 任意の NK / LK 導出に対し、対応する LF 証明項が存在すること、および逆に閉じた LF 証明項から NK / LK 導出を復元できること。
- **カット除去定理（Cut Elimination）**: カット規則を含む任意の LK 導出から、カット規則を含まない導出が得られること。

## 信頼境界と制限

- **対象範囲**: 原子命題、⊥、⊤、含意、連言、選言、否定を対象とします（量化子・等号は含みません）。
- **存在証明**: 導出やカット除去の「存在」の証明であり、実行可能な書き換えアルゴリズムではありません。
- **バイト列の対応**: 生成された pa バイト列と Rocq 内 AST の対応は未証明です（テストによる照合を実施）。

## TODO

- [ ] 一階述語論理（量化子・等号）への拡張
- [ ] 実行可能なカット除去変換器の実装と検証
- [ ] NK と LK の間の直接的な相互翻訳
