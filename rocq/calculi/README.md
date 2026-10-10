# 命題論理 NK / LK over proofglyph

古典命題論理の自然演繹（NK）とシーケント計算（LK）を、固定の proofglyph prelude と LF 証明項として符号化した検証です。
NK・LK の導出と proofglyph の証明項の対応関係、および LK のカット除去定理を Rocq で証明しています。

## ビルドと実行

```sh
# 検証とテスト
make -C rocq/calculi test

# proofglyph ファイルの生成と検査
make -C rocq/calculi export
dune exec bin/main.exe -- check rocq/calculi/_build/proofs.pg --prelude rocq/calculi/_build/prelude.pg
```

`export` は名前付きの `prelude.ht` / `proofs.ht` と、NK・LK 単独版の
`nk-prelude.ht` / `nk-proofs.ht`、`lk-prelude.ht` / `lk-proofs.ht` も生成します。
型・論理記号・判断の語彙は `symbol`、推論規則は `axiom`、証明済みの例は
`theorem` として出力します。共通 prelude は18個の `symbol` と38個の `axiom` です。
どちらの前提宣言もカーネルでは `Assume` となり、既存の `.pg` の内容は変わりません。
テストでは `.ht` のコンパイル結果と直接生成した `.pg` の一致も確認します。

## 証明した保証

- **導出と証明項の対応（Adequacy）**: 固定 LF シグネチャの下で、任意の NK / LK 導出に対し、対応する LF 証明項が存在すること、および逆に閉じた LF 証明項から NK / LK 導出を復元できること。
- **カット除去定理（Cut Elimination）**: カット規則を含む任意の LK 導出から、カット規則を含まない導出が得られること。

## 信頼境界と制限

- **対象範囲**: 原子命題、⊥、⊤、含意、連言、選言、否定を対象とします（量化子・等号は含みません）。
- **存在証明**: 導出やカット除去の「存在」の証明であり、実行可能な書き換えアルゴリズムではありません。
- **バイト列の対応**: 生成された proofglyph バイト列と Rocq 内 AST の対応は未証明です（テストによる照合を実施）。

## TODO

- [ ] 一階述語論理（量化子・等号）への拡張
- [ ] 実行可能なカット除去変換器の実装と検証
- [ ] NK と LK の間の直接的な相互翻訳
