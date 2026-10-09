# 証明ライブラリ

関連する定理を分野ごとの `.ht` モジュールにまとめています。利用したいモジュールを直接 `import` すれば、必要な定義と先行する証明も自動的に読み込まれます（全分野を一括で読み込む互換用のエントリーポイントは設けていません）。

`examples/` 内のファイルから加算の定理を使う例：

```text
import "commons/nat/addition.ht";

theorem commute_example (a b : Nat) : Prf (Eq (add a b) (add b a))
  := add_comm a b;
```

どのモジュールも直接コンパイルして検査できます。

```sh
dune exec bin/main.exe -- compile examples/commons/nat/addition.ht -o /tmp/addition.pg
dune exec bin/main.exe -- check /tmp/addition.pg
```

## 構成

| 場所 | 内容 |
| --- | --- |
| [foundation/](foundation/) | 信頼する語彙、論理規則、Peano 公理、等式規則、述語と再帰関数の定義、集合の分出。分野別の17モジュール。 |
| [logic/propositional.ht](logic/propositional.ht) | 含意の合成、引数の交換・複製、連言・選言、対偶、構成的なド・モルガン則。 |
| [logic/classical.ht](logic/classical.ht) | 排中律を使うド・モルガン則の方向。 |
| [logic/quantifiers.ht](logic/quantifiers.ht) | 型 `U` 上の全称・存在量化、関数の合成。 |
| [equality.ht](equality.ht) | 型 `U` 上の等式の対称律・推移律・関数による保存。 |
| [nat/](nat/) | 自然数の等式、算術、順序、整数論の証明。25モジュール、137定理。 |
| [sets/russell.ht](sets/russell.ht) | 分出から導く普遍集合の非存在。排中律・選択公理は不要。 |

`foundation/` では、未定義の型・論理記号を `symbol`、信頼する論理・等式・Peano・再帰・分出の原理を `axiom`、演算や述語を `def`、定義から導く規則や方程式を `theorem` で記述します。`And`・`Or`・`Not`・`False`・`Exists`・`Divides`・`Prime`・順序・偶奇・合同式などの導入除去規則や、加算・乗算・累乗・和・二項係数などの方程式は証明済みです。再帰の公理は `recursion.ht` と `sums.ht` に明示し、Peano 公理だけから導出したとは主張しません。`symbol` もカーネル上では前提として数えます。各定理の詳細と証明の一覧は [証明カタログ](../../docs/proofs.md) を参照してください。

`import` は同じ実体ファイルを1度だけ読み込みます。名前空間は共通なので、型 `U` 上の `Eq`・量化と、自然数上の同名のシグネチャは別々に利用します。自然数の等式には `nat/basic.ht` を使用してください。

## 自然数・整数論のモジュール

| モジュール | 内容 |
| --- | --- |
| [basic.ht](nat/basic.ht) | 自然数の等式、場合分け、1・2の反射律。 |
| [addition.ht](nat/addition.ht) | 加算の単位元、後者、結合則、交換則、消去。 |
| [multiplication.ht](nat/multiplication.ht) | 乗算の単位元、分配則、結合則、交換則。 |
| [order.ht](nat/order.ht) | 加算による順序の定義からの比較、正値性、矛盾。 |
| [ordered_multiplication.ht](nat/ordered_multiplication.ht) | 正の数による乗算の消去、積の正値性。 |
| [powers.ht](nat/powers.ht) | 累乗の加法則、1の累乗、正指数の0の累乗。 |
| [parity.ht](nat/parity.ht) | 偶数同士・奇数同士の和。 |
| [sums.ht](nat/sums.ht) | 有限和の等式、添字の移動、三角数の公式、奇数の和と平方数。 |
| [divisibility.ht](nat/divisibility.ht) | 整除性の推移律、和・積への保存、加算からの消去。 |
| [congruence.ht](nat/congruence.ht) | 合同式の等式法則、加算・乗算・累乗による保存。 |
| [classical.ht](nat/classical.ht) | 排中律からの二重否定除去。 |
| [induction.ht](nat/induction.ht) | Peano の帰納法からの強い帰納法。 |
| [division.ht](nat/division.ht) | 最小の正の証人、除法の原理、最小の倍数の整除性。 |
| [primes.ht](nat/primes.ht) | 素数の正値性・約数、2の素数性、互いに素な数の補題。 |
| [factorization.ht](nat/factorization.ht) | 真の約数と素因数の存在。 |
| [euclid.ht](nat/euclid.ht) | ユークリッドの補題と平方の整除性。 |
| [prime_infinitude.ht](nat/prime_infinitude.ht) | 階乗の補題と素数の無限性。 |
| [binomial_coefficients.ht](nat/binomial_coefficients.ht) | 二項係数の範囲・対角・両端、パスカルの関係、係数の恒等式。 |
| [diagonal.ht](nat/diagonal.ht) | 対角有限和の等式、加法性、添字の移動。 |
| [convolution.ht](nat/convolution.ht) | 二項係数付き有限和の再帰式、等式・スカラー・単位元の補題。 |
| [binomial_theorem.ht](nat/binomial_theorem.ht) | 二項定理と一方の変数を1にした形。 |
| [prime_binomial.ht](nat/prime_binomial.ht) | 素数による内側の二項係数の整除性。 |
| [modular_sums.ht](nat/modular_sums.ht) | 開区間の有限和の合同保存。 |
| [fermat.ht](nat/fermat.ht) | 二項展開の合同補題、フェルマーの小定理、和への適用。 |
| [sqrt_two.ht](nat/sqrt_two.ht) | 平方の偶奇、互いに素な場合の矛盾、無限降下による√2の無理性。 |

自然数の基本的な依存関係は `basic → addition → multiplication` であり、順序や整除性などがその上に続きます。各証明の正確な依存関係は各ファイルの冒頭に記載されています。利用例は [論理の合成](../logic.ht) と [フェルマーの適用](../fermat_application.ht) を参照してください。
