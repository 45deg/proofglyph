# ZFC over pa — 符号化の正しさに向けた独立開発

完全性の開発から分離した開発です。ZFC の全公理・公理図式と、独立した自然演繹の証明体系を
Rocq に定義しました。**閉じた式について、ZFC の証明可能性と固定 prelude の下での pa 項の受理との同値性を Rocq で証明しました。** Zorn の補題も未実装です。
既存の `rocq4pa/` の定義は変更せず、その検査器・健全性・完全性定理を利用します。
完全性側の変更はコミット `16816eb` まで取り込み済みです。

## 実装したもの

- `Formula.v`: 関数記号を持たない一階集合論の式。変数は de Bruijn index。
  等号・所属・偽・含意・全称量化を基本とし、他の結合子を古典論理での略記として定義。
  閉じた式の判定と、外延性・空集合・対集合の文を定義。
- `Axioms.v`: 外延性・空集合・対・和集合・冪集合・無限・基礎・選択と、パラメータ付きの
  分出・置換図式を定義。`zfc_axiom` は構文的な述語で、Rocq の `Axiom` ではありません。
  `all_axioms_closed` によりすべての公理インスタンスが閉じた文であることを証明。
- `Semantics.v`: 任意の領域・所属関係での解釈を定義。変数変更・閉じた文の環境独立性、
  各公理と通常の集合論の主張との対応を証明。分出・置換は自由パラメータの全称閉包まで対象。
- `Deduction.v`: 古典一階自然演繹、量化子の一般化・具体化、等号の反射・置換から
  独立した `ZFC_proves` を定義。証明で変数範囲が保たれることと、意味論的健全性を証明。
  一般化では全仮定を持ち上げ、代入では binder の下で変数写像を持ち上げます。
  全称量化された等号の対称律・推移律もこの体系内で導出しています。
- `Specification.v`: 完成版の固定署名が満たすべき `correct_presentation` を定義。
  `declarative_presentation` からこの契約と証明可能性の同値性を導出済みです。
  `typed_translation_accepted` は証明翻訳の型付けから、十分な fuel すべてでの受理を導きます。
  `Reflection.v` の `concrete_correct_presentation` が、この契約の具体的な実装です。
- `Encoding.v`: 上記の構文を pa の項へ埋め込む深い符号化。
  任意の式の往復変換 `formula_roundtrip`、単射性 `encode_injective`、
  型付け `encode_typed`、構文用 prelude の整形式性を Rocq で証明。
  これらは式の構文の性質であり、式の証明可能性の対応ではありません。
- `prelude.tp`: 既存の一階論理・等式規則に所属関係、外延性、空集合の存在、対集合の存在を追加。
  ZFC の初期断片です。分出・置換を任意の高階述語で代用する宣言は置いていません。
- `proof_prelude.tp`: 全 ZFC を対象とする83宣言の固定 prelude。最初の9宣言は
  `Encoding.v` の式の構文と同一です。変数範囲、binder を避けた変数変更、全称閉包、
  仮定の持ち上げを証拠として要求し、8公理・分出・置換と自然演繹の10規則を表します。
  分出は置換・空集合から導出可能な冗長な公理ですが、現在の `zfc_axiom` と直接対応するため
  基本規則として残しています。その体系内導出を証明するまでは削除しません。
- `Certificates.v`: prelude の変数変更・全称閉包・仮定の持ち上げを表す構造的な証拠を定義し、
  各操作との一致、`axiom_certificate_iff`、`proof_certificate_iff` を証明。
  この証拠と LF の型付き項との対応は `Translation.v` と `Reflection.v` で証明しました。
- `DeepVerification.v`: 実際に出力した全理論 prelude の整形式性、式の構文の接頭辞、
  8公理と分出・置換規則の型の一致、すべての式についての `proof_type_sorted` を証明。
  13個の証明・証拠の受理と、本体に公理追加がないことも検証します。
- `Translation.v`: すべての構造的な証拠から閉じた型付き pa 項の存在を導出。
  `certificate_translation`、`ZFC_translation` と、十分な fuel すべてでの受理を示す
  `ZFC_accepted` を証明しました。具体例に限定した定理ではありません。
- `GroundAdequacy.v`: 関数を引数に取らない一階の LF 署名について、正規形の閉じた原子型の項を
  定数と適用からなる木として復元する一般定理 `normal_atomic_ground` を証明。
- `Reflection.v`: 実際の固定署名が一階であることと、83宣言の各意味を検証。
  `typed_proof_recovered` は任意の型付き pa 項を正規化し、`proof_certificate` を復元します。
  `ZFC_pa_iff` により目標の同値性を証明しました。Rocq の新しい公理には依存しません。
- `proof_certificates.tp`: 8公理、分出・置換インスタンス、等号の反射、含意の恒等証明、
  binder 下の変数変更を実際の pa 項で確認する例です。
- `basic.tp`: 等式の対称性、空集合の一意性、その量化版、非空集合と空集合の不一致、
  対集合の所属条件における要素順序の交換。5宣言すべて証明付きで、新しい公理なし。
- `export.ml`: 実際の `.tp` 宣言から固定 prelude と証明本体の `.pa`、同じ解決済み AST の
  Rocq データを生成。元のコンパイラによる検査も通す。
- `Verification.v`: 生成した証明項を Rocq 内で実行して検査し、型付け導出の存在と
  公理追加がないことを既存の健全性定理から証明。

`prelude.tp` と `basic.tp` は従来の高階抽象構文による3公理の例として残しています。
同値性の証明対象は、明示的な一階論理式と変数条件を扱う `proof_prelude.tp` です。
その公理と図式の型の一致、および任意の LF 証明項を含む対応を証明しました。

## 採用した公理の形と意味論

選択公理は「互いに素な非空集合族に対して、各集合とちょうど一点で交わる集合が存在する」
という形です。[MIT の講義資料（Problem 7.28）](https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-spring-2015/mit6_042js15_session11.pdf)
にも同じ形が記載されています。選択関数版との同値性をこの開発で証明したわけではありません。

分出の式 phi の自由変数は `[x, parameters...]`、置換の式 theta は `[y, x, parameters...]`。
公理図式を作る際に増える binder を避けてパラメータを移し、最後に全パラメータを全称量化します。
`separation_meaning` / `replacement_meaning` は、この index 操作が意図した主張を表すことを示します。

意味論的健全性 `ZFC_proves_sound` は、**古典論理（二重否定除去）と、その解釈が全 ZFC 公理を
満たすという明示的な前提の下**での定理です。ZFC のモデルの存在・無矛盾性を証明したものでは
ありません。これらの前提は定理の引数であり、新たなグローバル公理は追加していません。

## 検証

```sh
make -C zfc test ROCQ=/path/to/bin/rocq
```

この作業環境の検証には次を使っています。

```sh
make -C zfc test ROCQ=/private/tmp/rocq4pa-toolchain/_opam/bin/rocq
```

全理論の生成物は `zfc/_build/deep/`、従来の3公理の生成物は `zfc/_build/`。`prelude.pa` を先に読み込み、`proofs.pa` 内では `:` を禁止します。

```sh
rocq4pa/_build/rocq4pa check zfc/_build/deep/proofs.pa --prelude zfc/_build/deep/prelude.pa
```

`make test` は Rocq のコンパイルと `rocq check`、OCaml 版・Rocq 抽出版の両方での
本体再検査、公理混入や不正な証明の拒否を確認します。前提名の許可一覧も固定しています。

## 証明した同値性

Rocq で独立に定義した一階論理と ZFC の証明述語 `ZFC_proves` に対し、閉じた式 φ について、

```text
ZFC_proves φ
  ↔ ∃ proof fuel,
      check fuel zfc_signature proof (proof_type φ) = true
```

を `ZfcDeep.Reflection.ZFC_pa_iff` で証明しました。健全性側は翻訳で生成した項だけでなく、
任意の受理された証明項を対象にします。完全性側は ZFC の有限証明から pa の証明項の存在と
型付けを導出し、十分な fuel が存在することを示します。
`Print Assumptions ZFC_pa_iff` の結果は `Closed under the global context` です。

逆方向では、型付き項の正規化、正規形からの定数・適用の木の復元、
各定数の意味に基づく構造的な証拠の復元を順に行います。
これは式のコードの型付けだけを示す `encode_typed` より強い定理です。

残る作業は、実際のバイト列と Rocq 内の AST の対応の形式検証と、
分出を置換・空集合から体系内で導出して基本規則から取り除くことです。

公理の無矛盾性は主張しません。手書きの出力器・パーサー、Rocq の抽出と OCaml 実行系は
信頼境界に残ります。生成データの Rocq 再検査は、出力器が意図した命題を正しく翻訳したことの
証明を代替しません。

## 検査器の完全性との接続

`Checker.declarative_check_complete` の前提は、署名の整形式性、目標型の sort、
閉じた証明項の宣言的型付けです。結論は、ある自然数の境界以上のすべての fuel での受理です。
`Specification.v` の接続定理はこの定理を直接使用し、停止性や公理の無矛盾性、
古典論理・モデルの存在を追加の前提にしていません。
ZFC の証明から文の閉性は `provable_sentence` で導きます。

逆方向には、整形式の署名の下で `Checker.check_sound` により型付けを取り出します。
固定署名の整形式性・目標型の sort は `DeepVerification.v` で証明しました。
ZFC 証明と任意の型付き証明項との対応は `Translation.v` と `Reflection.v` で証明しました。
この同値性は Rocq 内の AST に対する定理であり、CLI の入出力全体の形式検証ではありません。
fuel の結論は Rocq の自然数についてであり、CLI の fuel 上限や実機資源内の成功は保証しません。
