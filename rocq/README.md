# Rocq による形式証明

tinyprover に関連する Rocq（旧 Coq）の定義・証明、抽出用コード、生成器、テストをここにまとめています。
通常の OCaml ビルドには Rocq は不要です。

| ディレクトリ | 名前空間 | 対象 |
| --- | --- | --- |
| [pa/](pa/README.md) | `Tinyprover.Pa` | 核心言語、型付け、検査器の健全性・完全性 |
| [tp/](tp/README.md) | `Tinyprover.Tp` | 名前付き言語の解析・変換とその検証 |
| [calculi/](calculi/README.md) | `Tinyprover.Calculi` | NK・LK、LFとの対応、カット除去 |
| [zfc/](zfc/README.md) | `Tinyprover.Zfc` | ZFCの証明体系とpa符号化の対応 |

`tp`、`calculi`、`zfc` は `pa` に依存します。
ZFCの全理論とRussellの生成物には、それぞれ `Tinyprover.ZfcDeep` と
`Tinyprover.ZfcRussell` を使います。証明済みの範囲と信頼する前提は、各READMEに記載しています。

## 実行

リポジトリのルートで次を実行します。Rocq・OCaml・Duneと、テスト用のPython 3が必要です。

```sh
make -C rocq verify
make -C rocq test
```

`verify` は全開発のRocqコンパイルと `rocq check` を実行します。
`test` はこれに加え、抽出した実行ファイルと既存のOCaml実装によるテストを実行します。
各開発のMakefileが依存する `pa` を先に検証します。

個別に実行する場合は、次のように指定します。

```sh
make -C rocq/pa test
make -C rocq/tp test
make -C rocq/calculi test
make -C rocq/zfc test
```

`ROCQ=/path/to/bin/rocq` と `OCAMLC=/path/to/bin/ocamlc` でツールを指定できます。
生成された `.v`、コンパイル結果、抽出コード、pa証明は各ディレクトリの `_build/` に置きます。
抽出した実行ファイルの名前は `rocq4pa`・`rocq4tp` を維持しています。

```sh
rocq/pa/_build/rocq4pa check examples/identity.pa
rocq/tp/_build/rocq4tp check examples/basics.tp
```
