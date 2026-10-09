# Rocq による形式証明

tinyprover に関連する Rocq（旧 Coq）の形式証明、抽出コード、テストをまとめています。
通常の OCaml ビルドには Rocq は不要です。

| サブプロジェクト | 名前空間 | 対象 |
| --- | --- | --- |
| [proofglyph/](proofglyph/README.md) | `Tinyprover.Proofglyph` | 核心言語の型付け、検査器の健全性・完全性 |
| [hieratic/](hieratic/README.md) | `Tinyprover.Hieratic` | 高水準言語の解析・変換・import 展開の検証 |
| [calculi/](calculi/README.md) | `Tinyprover.Calculi` | 命題論理 NK・LK、LF との対応、カット除去 |
| [zfc/](zfc/README.md) | `Tinyprover.Zfc` | ZFC 証明体系と proofglyph 符号化の同値性 |

## 検証と実行

Rocq、OCaml、Dune、Make、Python 3、および抽出 CLI 用の ocamlfind と Zarith が必要です。

```sh
# 全サブプロジェクトの検証とテスト
make -C rocq verify
make -C rocq test

# 抽出した CLI の実行
rocq/proofglyph/_build/proofglyph check examples/identity.pg
rocq/hieratic/_build/hieratic check examples/basics.ht
```

個別に実行する場合は `make -C rocq/proofglyph test` などを指定します。

proofglyph/hieratic のコンパイル順は各 `_CoqProject` で管理します。Make は証明を `_build/` にコピーし、抽出物を含む生成物をそこに隔離します。proofglyph/hieratic の検証済みスタンプにより、証明ソース・ビルド設定・依存する proofglyph の検証結果が更新された場合に再検証します。

通常の OCaml 実装と証明入力のジェネレータは Dune、Rocq の検証と抽出 CLI のコンパイルは Make と `ocamlc` が担当します。抽出 CLI のビルドは、通常の Dune ビルドとは別に実行します。

## 設計方針

proofglyph および hieratic では、**言語仕様・実装・対応証明**を明確に分離しています。

- **言語仕様**: 構文、型付け規則、評価仕様（アルゴリズムに依存しない宣言的定義）
- **実装**: 検査器、変換器、パーサー、codec
- **対応証明**: 仕様と実装の一致、健全性・完全性定理

証明側では `nat` を使い、OCaml への抽出時に標準の `ExtrOcamlNatBigInt` で Zarith の多倍長整数へ置き換えます。単項自然数の確保と機械整数のオーバーフローを避けられますが、抽出時の演算の置換設定と Zarith は信頼境界に加わります。CLI の入力上限は資源消費を抑えるために維持します。自然数を減らしながら再帰する処理の計算量は、表現の変更だけでは改善しません。
