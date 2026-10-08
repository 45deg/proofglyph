# Rocq による形式証明

tinyprover に関連する Rocq（旧 Coq）の形式証明、抽出コード、テストをまとめています。
通常の OCaml ビルドには Rocq は不要です。

| サブプロジェクト | 名前空間 | 対象 |
| --- | --- | --- |
| [pa/](pa/README.md) | `Tinyprover.Pa` | 核心言語の型付け、検査器の健全性・完全性 |
| [tp/](tp/README.md) | `Tinyprover.Tp` | 高水準言語の解析・変換・import 展開の検証 |
| [calculi/](calculi/README.md) | `Tinyprover.Calculi` | 命題論理 NK・LK、LF との対応、カット除去 |
| [zfc/](zfc/README.md) | `Tinyprover.Zfc` | ZFC 証明体系と pa 符号化の同値性 |

## 検証と実行

Rocq、OCaml、Dune、Make、Python 3 が必要です。

```sh
# 全サブプロジェクトの検証とテスト
make -C rocq verify
make -C rocq test

# 抽出した CLI の実行
rocq/pa/_build/pa check examples/identity.pa
rocq/tp/_build/tp check examples/basics.tp
```

個別に実行する場合は `make -C rocq/pa test` などを指定します。

## 設計方針

pa および tp では、**言語仕様・実装・対応証明**を明確に分離しています。

- **言語仕様**: 構文、型付け規則、評価仕様（アルゴリズムに依存しない宣言的定義）
- **実装**: 検査器、変換器、パーサー、codec
- **対応証明**: 仕様と実装の一致、健全性・完全性定理
