# ZFC over proofglyph

一階論理上の ZFC 公理系と自然演繹体系を Rocq で定義し、**閉じた式について、ZFC の証明可能性と固定 LF シグネチャ上の型付き証明項の存在が同値であること**を形式証明した検証です。

## ビルドと実行

```sh
# 検証とテスト
make -C rocq/zfc test

# Russell の例（普遍集合の非存在）の検査
rocq/proofglyph/_build/proofglyph check rocq/zfc/_build/russell/proofs.pg --prelude rocq/zfc/_build/russell/prelude.pg
```

## 証明した保証

- **同値性定理（`ZFC_proofglyph_iff`）**: 任意の閉じた式 $\phi$ に対し、ZFC で証明可能であることと、Rocq 内で定義した固定 LF シグネチャ上の型付き proofglyph 項が存在することが同値（追加公理や `Admitted` は使用していません）。
- **具体例の検証**: ラッセルのパラドックスに基づく「普遍集合の非存在（$\neg \exists U, \forall x, x \in U$）」の導出を proofglyph 項として生成し、実際に受理されることを検証。

## 公理の削減

完全版の `zfc_axiom` と `proof_prelude.ht` から空集合公理を除去しました。固定公理は 8 個から 7 個となり、分出・置換の公理図式は維持しています。

`Empty.v` の `empty_set_derived` は、無限公理に含まれる「空集合を要素として持つ」という条件から、任意の変数深さ・仮定の下で空集合の存在を導きます。従来の空集合公理の使用箇所をこの導出で置き換えられます。`empty_set_not_primitive` は空集合が基本公理でないことを検証します。

`empty_export.py` は `proof_certificates.ht` のマーカーにこの導出の証明項を挿入し、`_build/deep/source.ht` を生成します。生成結果は Rocq と二つの検査器で検証します。従来の小さな例示用 `prelude.ht` は無限公理を含まないため、`empty_exists` を維持しています。

## 信頼境界と制限

- **公理の無矛盾性**: ZFC 公理系自体の無矛盾性やモデルの存在を証明したものではありません。
- **バイト列の対応**: 生成された proofglyph バイト列と Rocq 内 AST の対応は形式検証していません（テストによる照合を実施）。

## TODO

- [x] 空集合公理を無限公理から体系内で導出し、完全版の基本規則から除去する
- [ ] 実際の proofglyph 出力バイト列と Rocq 内 AST の対応関係の形式検証
- [ ] 選択関数版の選択公理との同値性証明
