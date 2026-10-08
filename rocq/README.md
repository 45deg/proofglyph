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
抽出した実行ファイルの名前は `pa`・`tp` です。通常の CLI とは別のビルド先に置きます。

```sh
rocq/pa/_build/pa check examples/identity.pa
rocq/tp/_build/tp check examples/basics.tp
```

## モジュールの境界

pa・tp の開発は、言語仕様・実装・対応証明を分けています。
言語仕様はアルゴリズムや検査器に依存せず、実装は仕様と他の実装だけに依存します。
対応証明が両者を接続します。既存の入口モジュールは分離した定義を再エクスポートします。

| 層 | pa | tp |
| --- | --- | --- |
| 言語仕様・性質 | `Syntax`、`Program`、整形式性・置換・型保存・合流性・強正規化、`EvaluationSpec`、`CheckerSpec`、`CodecSpec` | `Surface`、`DesugarSpec`、`ResolveSpec`、`CompileSpec`、`TpSyntaxSpec`、`TpImportsSpec`、`FileSpec` |
| 実装 | `KernelImpl`、`CheckerImpl`、`CodecImpl` | `DesugarImpl`、`ResolveImpl`、`CompileImpl`、`TpSyntaxImpl`、`TpImportsImpl`、`PaCompileImpl`、`SurfaceCompileImpl`、`FileImpl` |
| 対応証明 | `Kernel`、`Evaluation`、`Checker`、`CodecCorrectness`、`Codec`、`ConfluenceCorrectness`、`PreservationCorrectness` | `Desugar`、`Resolve`、`Compile`、`TpSyntax`、`TpImports`、`PaCompile`、`SurfaceCompile`、`FileCompile` |

`make test` は `test_layers.py` で依存の境界も検査します。
通常の OCaml CLI・Web は従来の実装を使います。
