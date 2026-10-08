# ZFC over pa

一階論理上の ZFC 公理系と自然演繹体系を Rocq で定義し、**「閉じた式について、ZFC の証明可能性と tinyprover（固定 prelude）で受理される証明項の存在が同値であること」**を形式証明した検証です。

## ビルドと実行

```sh
# 検証とテスト
make -C rocq/zfc test

# Russell の例（普遍集合の非存在）の検査
rocq/pa/_build/pa check rocq/zfc/_build/russell/proofs.pa --prelude rocq/zfc/_build/russell/prelude.pa
```

## 証明した保証

- **同値性定理（`ZFC_pa_iff`）**: 任意の閉じた式 $\phi$ に対し、ZFC で証明可能であることと、固定 prelude の下で受理される型付き pa 項が存在することが同値（追加公理や `Admitted` は使用していません）。
- **具体例の検証**: ラッセルのパラドックスに基づく「普遍集合の非存在（$\neg \exists U, \forall x, x \in U$）」の導出を pa 項として生成し、実際に受理されることを検証。

## 信頼境界と制限

- **公理の無矛盾性**: ZFC 公理系自体の無矛盾性やモデルの存在を証明したものではありません。
- **バイト列の対応**: 生成された pa バイト列と Rocq 内 AST の対応は形式検証していません（テストによる照合を実施）。

## TODO

- [ ] 分出公理を図式と空集合から体系内で導出し、基本規則から冗長性を排除する
- [ ] 実際の pa 出力バイト列と Rocq 内 AST の対応関係の形式検証
- [ ] 選択関数版の選択公理との同値性証明
