# 証明ライブラリ

関連する定理を分野ごとの `.tp` モジュールにまとめています。利用したいモジュールを直接 `import` すれば、必要な定義と先行する証明も自動的に読み込まれます（全分野を一括で読み込む互換用のエントリーポイントは設けていません）。

`examples/` 内のファイルから加算の定理を使う例：

```text
import "commons/nat/addition.tp";

theorem commute_example (a b : Nat) : Prf (Eq (add a b) (add b a))
  := add_comm a b;
```

どのモジュールも直接コンパイルして検査できます。

```sh
dune exec bin/main.exe -- compile examples/commons/nat/addition.tp -o /tmp/addition.pa
dune exec bin/main.exe -- check /tmp/addition.pa
```

## 構成

| 場所 | 内容 |
| --- | --- |
| [foundation/](foundation/) | 信頼する語彙、論理規則、Peano 公理、等式規則、述語と再帰関数の定義。分野別の15モジュール。 |
| [logic/propositional.tp](logic/propositional.tp) | 含意の合成、引数の交換・複製、連言・選言、対偶、構成的なド・モルガン則。 |
| [logic/classical.tp](logic/classical.tp) | 排中律を使うド・モルガン則の方向。 |
| [logic/quantifiers.tp](logic/quantifiers.tp) | 型 `U` 上の全称・存在量化、関数の合成。 |
| [equality.tp](equality.tp) | 型 `U` 上の等式の対称律・推移律・関数による保存。 |
| [nat/](nat/) | 自然数の等式、算術、順序、整数論の証明。25モジュール、135定理。 |

`foundation/` のファイルは `axiom` 宣言、残りは `theorem` 宣言を持ちます。`axiom` は記号や定義の方程式を登録するためにも使用し、数学的な補題を仮定する宣言は置いていません。各定理の詳細と証明の一覧は [証明カタログ](../../docs/proofs.md) を参照してください。

`import` は同じ実体ファイルを1度だけ読み込みます。名前空間は共通なので、型 `U` 上の `Eq`・量化と、自然数上の同名のシグネチャは別々に利用します。自然数の等式には `nat/basic.tp` を使用してください。

## 自然数・整数論のモジュール

| モジュール | 内容 |
| --- | --- |
| [basic.tp](nat/basic.tp) | 自然数の等式、場合分け、1・2の反射律。 |
| [addition.tp](nat/addition.tp) | 加算の単位元、後者、結合則、交換則、消去。 |
| [multiplication.tp](nat/multiplication.tp) | 乗算の単位元、分配則、結合則、交換則。 |
| [order.tp](nat/order.tp) | 加算による順序の定義からの比較、正値性、矛盾。 |
| [ordered_multiplication.tp](nat/ordered_multiplication.tp) | 正の数による乗算の消去、積の正値性。 |
| [powers.tp](nat/powers.tp) | 累乗の加法則、1の累乗、正指数の0の累乗。 |
| [parity.tp](nat/parity.tp) | 偶数同士・奇数同士の和。 |
| [sums.tp](nat/sums.tp) | 有限和の等式、添字の移動、三角数の公式。 |
| [divisibility.tp](nat/divisibility.tp) | 整除性の推移律、和・積への保存、加算からの消去。 |
| [congruence.tp](nat/congruence.tp) | 合同式の等式法則、加算・乗算・累乗による保存。 |
| [classical.tp](nat/classical.tp) | 排中律からの二重否定除去。 |
| [induction.tp](nat/induction.tp) | Peano の帰納法からの強い帰納法。 |
| [division.tp](nat/division.tp) | 最小の正の証人、除法の原理、最小の倍数の整除性。 |
| [primes.tp](nat/primes.tp) | 素数の正値性・約数、2の素数性、互いに素な数の補題。 |
| [factorization.tp](nat/factorization.tp) | 真の約数と素因数の存在。 |
| [euclid.tp](nat/euclid.tp) | ユークリッドの補題と平方の整除性。 |
| [prime_infinitude.tp](nat/prime_infinitude.tp) | 階乗の補題と素数の無限性。 |
| [binomial_coefficients.tp](nat/binomial_coefficients.tp) | 二項係数の範囲・対角・両端、パスカルの関係、係数の恒等式。 |
| [diagonal.tp](nat/diagonal.tp) | 対角有限和の等式、加法性、添字の移動。 |
| [convolution.tp](nat/convolution.tp) | 二項係数付き有限和の再帰式、等式・スカラー・単位元の補題。 |
| [binomial_theorem.tp](nat/binomial_theorem.tp) | 二項定理と一方の変数を1にした形。 |
| [prime_binomial.tp](nat/prime_binomial.tp) | 素数による内側の二項係数の整除性。 |
| [modular_sums.tp](nat/modular_sums.tp) | 開区間の有限和の合同保存。 |
| [fermat.tp](nat/fermat.tp) | 二項展開の合同補題、フェルマーの小定理、和への適用。 |
| [sqrt_two.tp](nat/sqrt_two.tp) | 平方の偶奇、互いに素な場合の矛盾、無限降下による√2の無理性。 |

自然数の基本的な依存関係は `basic → addition → multiplication` であり、順序や整除性などがその上に続きます。各証明の正確な依存関係は各ファイルの冒頭に記載されています。利用例は [論理の合成](../logic.tp) と [フェルマーの適用](../fermat_application.tp) を参照してください。
