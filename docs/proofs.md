# 証明カタログ

`examples/commons/` には、論理・等式・自然数・整数論などの規則・定義・定理を分野別のモジュールとして収録しています。算術の土台は Peano 公理、論理・等式の推論規則、原始再帰の公理、および明示的な述語・演算の定義に限定し、すべての定理はこれらから導出された証明項として記述されています。

- [命題論理](../examples/commons/logic/propositional.ht): 含意、連言、選言、対偶、構成的なド・モルガン則。古典論理と量化は別モジュール。
- [普遍集合の非存在](../examples/commons/sets/russell.ht): 分出と論理規則から導くラッセルの議論。
- [等式](../examples/commons/equality.ht): 固定した型 `U` 上の反射律と置換から導出する3定理。
- [ライブラリの構成](../examples/commons/README.md): 加算、乗算、順序、整除性、合同式、素数、有限和など、用途に応じたモジュール。
- [Peano の土台](../examples/commons/foundation/peano.ht): 自然数の記号、等式、帰納法、後者関数の単射性と0との区別。
- [フェルマーの利用例](../examples/fermat_application.ht): 証明済みの小定理を import し、和に適用する定理。

`examples/commons/foundation/` は前提となる語彙・公理・定義を含み、`examples/commons/logic/`、`examples/commons/equality.ht`、`examples/commons/nat/`、`examples/commons/sets/` はそれらに基づいて型検査される証明項です。証明ファイル自体には `axiom` を含みません。`def` の本体は Hieratic のコンパイル時に展開します。`theorem` は不透明な参照を保持します。カーネルでは β 同値を使い、演算の再帰計算は対応する等式の証明項で扱います。

## 実装した証明

式中の `A → B` は証明の関数型 `Prf A -> Prf B`、`¬A` は `Not A` を表します。各宣言名のリンクから、個々の証明項と依存関係を参照できます。

<!-- proof-catalog:start -->

| 分野 | 命題・操作 | 宣言名 | ファイル |
| --- | --- | --- | --- |
| 入門 | 恒等関数・依存型・β同値 | [id](../examples/basics.ht), [dependent_id](../examples/basics.ht), [beta](../examples/basics.ht) | `basics.ht` |
| 入門 | 証明済みの含意の合成を使う | [composition_example](../examples/logic.ht) | `logic.ht` |
| 論理 | 含意の合成 `(A → B) → (B → C) → A → C` | [implication_composition](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| 論理 | 引数の交換・複製、関数の合成 | [exchange](../examples/commons/logic/propositional.ht), [duplicate](../examples/commons/logic/propositional.ht), [function_composition](../examples/commons/logic/quantifiers.ht) | `logic/propositional.ht`, `logic/quantifiers.ht` |
| 論理 | 連言の交換則・結合則（両方向） | [and_comm](../examples/commons/logic/propositional.ht), [and_assoc_forward](../examples/commons/logic/propositional.ht), [and_assoc_backward](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| 論理 | 選言の交換則・場合分け | [or_comm](../examples/commons/logic/propositional.ht), [cases](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| 論理 | 対偶 `(A → B) → (¬B → ¬A)` | [contraposition](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| 論理 | ド・モルガン則 `¬(A ∨ B) ⇔ (¬A ∧ ¬B)`、`¬(A ∧ B) ⇔ (¬A ∨ ¬B)` | [demorgan_or_forward](../examples/commons/logic/demorgan.ht), [demorgan_or_backward](../examples/commons/logic/demorgan.ht), [demorgan_and_forward](../examples/commons/logic/demorgan.ht), [demorgan_and_backward](../examples/commons/logic/demorgan.ht) | `logic/demorgan.ht` |
| 論理 | 全称の具体化・存在への証人導入 | [forall_specialize](../examples/commons/logic/quantifiers.ht), [exists_witness](../examples/commons/logic/quantifiers.ht), [forall_to_exists](../examples/commons/logic/quantifiers.ht) | `logic/quantifiers.ht` |
| 等式 | 対称律・推移律・関数による保存 | [eq_sym](../examples/commons/equality.ht), [eq_trans](../examples/commons/equality.ht), [eq_cong](../examples/commons/equality.ht) | `equality.ht` |
| 自然数 | 強い帰納法 | [nat_strong_induction](../examples/commons/nat/induction.ht) | `nat/induction.ht` |
| 自然数 | `0 + n = n`, `n + 0 = n` | [add_zero_left](../examples/commons/nat/addition.ht), [add_zero_right](../examples/commons/nat/addition.ht) | `nat/addition.ht` |
| 自然数 | 加算の結合則・交換則 | [add_assoc](../examples/commons/nat/addition.ht), [add_comm](../examples/commons/nat/addition.ht) | `nat/addition.ht` |
| 自然数 | 乗算の分配則（両側）・結合則・交換則 | [mul_add_left](../examples/commons/nat/multiplication.ht), [mul_add_right](../examples/commons/nat/multiplication.ht), [mul_assoc](../examples/commons/nat/multiplication.ht), [mul_comm](../examples/commons/nat/multiplication.ht) | `nat/multiplication.ht` |
| 自然数 | `a^(m+n) = a^m a^n` | [pow_add](../examples/commons/nat/powers.ht) | `nat/powers.ht` |
| 自然数 | 偶数同士・奇数同士の和は偶数 | [even_add](../examples/commons/nat/parity.ht), [odd_add](../examples/commons/nat/parity.ht) | `nat/parity.ht` |
| 自然数 | `2Σ(k=1..n) k = n(n+1)` | [triangular_double](../examples/commons/nat/sums.ht) | `nat/sums.ht` |
| 自然数 | `1 + 3 + … + (2n−1) = n²` | [odd_sum_square](../examples/commons/nat/sums.ht) | `nat/sums.ht` |
| 整数論 | 整除性の推移律・和・積への保存 | [divides_trans](../examples/commons/nat/divisibility.ht), [divides_add](../examples/commons/nat/divisibility.ht), [divides_mul_right](../examples/commons/nat/divisibility.ht), [divides_mul_left](../examples/commons/nat/divisibility.ht) | `nat/divisibility.ht` |
| 整数論 | 合同式の加算・乗算・累乗による保存 | [cong_add](../examples/commons/nat/congruence.ht), [cong_mul](../examples/commons/nat/congruence.ht), [cong_pow](../examples/commons/nat/congruence.ht) | `nat/congruence.ht` |
| 整数論 | 除法の原理（商と余りの存在） | [division_algorithm](../examples/commons/nat/division.ht) | `nat/division.ht` |
| 整数論 | 素因数の存在 | [prime_factor](../examples/commons/nat/factorization.ht) | `nat/factorization.ht` |
| 整数論 | ユークリッドの補題・平方の整除性 | [prime_mul_elim](../examples/commons/nat/euclid.ht), [prime_divides_square](../examples/commons/nat/euclid.ht) | `nat/euclid.ht` |
| 整数論 | 素数 `p` は `C(p,k)` を割り切る（`0 < k < p`） | [prime_divides_choose](../examples/commons/nat/prime_binomial.ht) | `nat/prime_binomial.ht` |
| 整数論 | 二項定理 | [binomial_theorem](../examples/commons/nat/binomial_theorem.ht) | `nat/binomial_theorem.ht` |
| 整数論 | 素数は無限に存在する | [primes_infinite](../examples/commons/nat/prime_infinitude.ht) | `nat/prime_infinitude.ht` |
| 整数論 | √2 の無理性 | [sqrt_two_coprime_contradiction](../examples/commons/nat/sqrt_two.ht), [sqrt_two_irrational](../examples/commons/nat/sqrt_two.ht) | `nat/sqrt_two.ht` |
| 整数論 | フェルマーの小定理と和への適用 | [fermat](../examples/commons/nat/fermat.ht), [fermat_sum](../examples/commons/nat/fermat.ht) | `nat/fermat.ht` |

| 集合論 | ラッセルのパラドックスから普遍集合の非存在を示す | [no_universal_set](../examples/commons/sets/russell.ht) | `sets/russell.ht` |

<!-- proof-catalog:end -->

なお、`function_composition` は `f, g : U -> U` と `x : U` から合成関数 `g (f x) : U` を構築するプログラム項であり、命題の証明項ではありません。

## axiom の位置づけ

`symbol` は未定義の型・記号、`axiom` は信頼する原理、`def` は本体を持つ定義、`theorem` は証明項を持つ定理です。`symbol` と `axiom` は両方ともカーネル上の前提として数え、名前の変更だけで信頼範囲が減ったとは扱いません。

| 種類 | 宣言と内容 |
| --- | --- |
| 語彙 | `symbol`：`Nat`, `zero`, `succ`, `Prop`, `Prf`, `Eq`、論理記号と再帰子 |
| Peano と等式 | `axiom`：`nat_induction`, `succ_not_zero`, `eq_subst`（Nat / U）, `eq_refl`（Uのみ） |
| 論理 | `axiom`：含意・全称量化の基本規則、排中律 |
| 再帰 | `axiom`：関数型の原始再帰の基底／後続規則 |
| 集合 | `symbol Mem` と `axiom separation`：既存の集合の部分集合を作る分出 |
| 定義と導出 | `def`：`Divides`, `Prime` などの述語と演算。`theorem`：その導入／除去規則・再帰方程式 |

`And`・`Or`・`False` は含意と命題についての全称量化による Church 符号化、`Not A` は `Imp A False`、`Exists` は全称量化と含意による定義です。それぞれの導入・除去規則は `theorem` として検査します。`succ_injective` も再帰子が与える左逆から証明し、公理にはしません。自然数の `eq_refl` も再帰の基底方程式と置換から証明します。命題についての全称量化は新しく明示した原理であり、従来の公理から導いたとは主張しません。

たとえば `Divides d a` は `Exists (fun (k : Nat) => Eq a (mul d k))` と定義し、`divides_intro` / `divides_elim` は存在量化の規則から証明します。`Prime p` は「1より大きく、各約数が1または自分自身である数」と定義し、`prime_intro` / `prime_elim` は連言・含意・量化の規則から証明します。

基礎ファイル全体の証明を持たない規則・公理は75宣言から17宣言へ減らしました。語彙を含むカーネルの前提も116宣言から31宣言へ減っています。これはファイル全体の宣言数であり、異なるドメインの同名の等式・量化を含みます。各証明では必要なモジュールだけを読み込みます。

`proven` は、明示した前提の下で型検査された証明項を表します。再帰原理も前提に含むため、Peano 公理だけから再帰子の存在を証明したとは主張しません。新しい定義展開自体は既存の Rocq フロントエンド証明の対象外ですが、出力は独立した抽出検査器でも再検査します。

自然数についての全称量化 `AllNat` と列についての全称量化 `AllSeq` は、二変数の自然数関数についての量化 `AllBi` から定義します。関数の0での評価と定数関数への埋め込みを使い、それぞれの導入・除去規則を証明します。新しい量化原理は追加しません。

数値用再帰 `nat_rec` と列への再帰 `nat_rec_seq` は関数型の再帰子 `nat_rec_diagonal` から定義し、それぞれの2方程式を証明します。境界付き再帰 `bounded_rec` も定義です。再帰で計算する `lt_flag` が大小関係と一致することを帰納法で示し、基底・範囲内・範囲外の3方程式を証明します。この証明は排中律を使いません。同じ項・文脈の型検査結果を再利用し、展開量が増えても標準の検査予算で収録例を検査できます。17宣言の内訳は、含意・量化の規則8、等式規則3（自然数の置換とドメインUの反射・置換）、帰納法1、後者と0の非一致1、再帰方程式2、排中律1、分出1です。絶対的に最小の公理系であるとは主張しません。

自然数ライブラリの139個の `theorem` に加え、基礎ファイルにも定義から導いた証明を置いています。

### 自然数と再帰関数

1 は `succ zero`、2 は `succ (succ zero)` と表します。不透明な数値定数やそれを値と同一視する公理は用いず、`one_succ` や `two_succ` は反射律の定理として定義されています。

加算・乗算・累乗は次の再帰方程式を定義として持ちます。`pred`、`factorial`、`triangular` も同様に、0 と後者の場合を分けて定義します。

```text
add zero b = b
add (succ a) b = succ (add a b)
mul zero b = zero
mul (succ a) b = add b (mul a b)
pow a zero = 1
pow a (succ n) = mul a (pow a n)
pred zero = zero
pred (succ n) = n
factorial zero = 1
factorial (succ n) = mul (succ n) (factorial n)
triangular zero = zero
triangular (succ n) = add (triangular n) (succ n)
```

加算・乗算の結合則や交換則、累乗の加法則、三角数の公式などは帰納法から導出されます。[強い帰納法](../examples/commons/nat/induction.ht) も、通常の Peano 帰納法と順序の定義から導出される定理です。

### 奇数の和と平方数

[奇数の和](../examples/commons/nat/sums.ht)は `1 + 3 + … + (2n−1) = n²` を Peano 帰納法で証明します。`sum n f` は添字 `0` から `n−1` までの和なので、各項を `succ (add k k)`（`2k+1`）とします。`n=0` では空の和と `0²` がともに0です。帰納段階では、補題 `square_succ` の `(n+1)² = n² + (2n+1)` を使います。これは、正方形に次の奇数個の点からなるL字の縁を加える見方に対応します。新しい公理は追加していません。

### 述語の定義

導入・除去規則は、次の存在・全称による定義を表します。

```text
Le a b          ⇔ ∃k, b = a+k
Lt a b          ⇔ ∃k, b = a+succ k
Even n          ⇔ ∃k, n = k+k
Odd n           ⇔ ∃k, n = succ(k+k)
Divides d a     ⇔ ∃k, a = d*k
Cong a b m      ⇔ ∃x y, a+m*x = b+m*y
Prime p         ⇔ 1<p ∧ ∀d, d|p → (d=1 ∨ d=p)
Coprime a b     ⇔ ∀d, d|a → d|b → d=1
RationalRootTwo ⇔ ∃a b, 0<b ∧ a*a=2*(b*b)
```

合同式は自然数の切り捨て減算を避けるため、両側に倍数を足す定義を採用しています。整除性・合同式の推移律や演算による保存などは、証人と等式を構成して証明します。

### 素因数、ユークリッドの補題、無限性

[素因数の存在](../examples/commons/nat/factorization.ht) は、1 より大きい数が素数ならその数自身を取り、素数でなければ真の約数へ強い帰納法で降下します。真の約数の存在は素数の定義と古典論理から導出されます。

[除法の原理](../examples/commons/nat/division.ht) は、正の除数 `d` に対して `n = d * q + r`（`r < d`）を満たす `q, r` を強い帰納法で構成します。

[ユークリッドの補題](../examples/commons/nat/euclid.ht) は、`p | a * t` を満たす最小の正の `t` を取り、除法の原理と最小性から `t` が `p` と `b` を割り切ることを示します。素数の定義による `t = 1` または `t = p` の場合分けから `p | a` または `p | b` を導きます。

[素数の無限性](../examples/commons/nat/prime_infinitude.ht) は `n! + 1` の素因数を取ります。もしそれが `n` 以下であれば、階乗と `n! + 1` の両方を割り切るため 1 を割り切ることになり矛盾します。

### 二項係数と有限和

二項係数の定義は、境界値とパスカルの再帰方程式です。

```text
choose n zero = 1
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n k + choose n (succ k)
```

[係数の恒等式](../examples/commons/nat/binomial_coefficients.ht) は、先に `choose_balance` で `(k+1)*C(n+1,k+1)=(n+1)*C(n,k)` を帰納法で証明し、正の添字を後者の形に移します。ユークリッドの補題と素数の整除性から `prime_divides_choose` を導出します。

有限和には、通常の接頭和 `sum`、開区間の和 `sum_between`、`i+j=n` の対角線上の和 `diagonal` を定義しています。対角和は次の再帰方程式を持ちます。

```text
diagonal zero h = h zero zero
diagonal (succ n) h
  = diagonal n (i,j ↦ h i (succ j)) + h (succ n) zero
```

`convolution` は、この対角和を用いた定義です。

```text
convolution n f g = diagonal n (i,j ↦ C(n,i)*f(i)*g(j))
                 = Σ(i+j=n) C(n,i)*f(i)*g(j)
```

パスカルの関係式に対応する `convolution_pascal`、基底の `convolution_zero`、外延性、係数の取り出し、両端の分離はいずれも定理です。パスカルの式を公理として仮定するのではなく、二項係数の再帰と対角和の性質から導出しています。

[二項定理](../examples/commons/nat/binomial_theorem.ht) はこれらの補題、累乗の再帰、分配則から `n` の帰納法で証明します。開区間の和の合同保存も、その和の再帰定義と順序の比較から帰納法で証明します。

### √2 の無理性

[sqrt_two_no_positive_fraction](../examples/commons/nat/sqrt_two.ht) は、任意の自然数 `a, b` に対して `b > 0` と `a * a = 2 * (b * b)` から矛盾を導きます。既約分数への変換や互いに素であることを仮定しません。

ユークリッドの補題と 2 の素数性から `a` と `b` がともに 2 の倍数であることを示し、`a = 2k`, `b = 2j` と置きます。2 を消去すると `k * k = 2 * (j * j)` となり、`0 < j < b` であるため分母に関する強い帰納法により矛盾が導かれます。`sqrt_two_irrational` はこの定理から有理数表示の存在を排除します。

### 論理と古典性

論理・等式のモジュールも基本規則から導出されます。論理の量化は固定した型 `U` 上、算術の量化は `Nat` 上で行い、有限和の証明には自然数値の関数を量化する規則も用います。

ド・モルガン則のうち `¬(A ∧ B) → ¬A ∨ ¬B` の証明には排中律を用います（他の3方向および対偶は直観主義論理の範囲で構成的です）。算術ライブラリにおいても、素因数の存在、最小の正の証人、ユークリッドの補題などの一部の定理では古典論理を用いて証明しています。

## フェルマーの小定理

[fermat](../examples/commons/nat/fermat.ht) は、以下の順で証明します。

1. `prime_divides_choose` から、二項展開の内側の各項が 0 と合同になる。
2. `sum_between_cong_zero` で内側の和も 0 と合同になる。
3. `binomial_theorem` と証明済みの両端分離から、`(x+1)^p ≡ x^p+1 (mod p)` を得る。
4. 帰納法の仮定 `x^p ≡ x` を使い、後者の式へ移す。
5. 素数の正値性と `pow_zero_positive` を基底として、自然数の帰納法を適用する。

[fermat_sum](../examples/commons/nat/fermat.ht) は、証明済みの小定理に `x = a + b` を代入します。利用例の `fermat_application` はこの定理を import して適用します。

## 検証

公理の独立したモデル検証は [rocq/example_axioms](../rocq/example_axioms/README.md) にあります。自然数・論理の標準的な解釈と、分出の断片を満たす空の所属関係のモデルを Rocq で検査します。排中律は Rocq の `classic` に依存します。`.ht` と Rocq の型の対応は手作業であり、一般的な意味保存の証明は含みません。

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/commons/nat/fermat.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
# 分野別モジュールを単独で検査できる
dune exec bin/main.exe -- compile examples/commons/nat/euclid.ht -o /tmp/euclid.pg
dune exec bin/main.exe -- check /tmp/euclid.pg
```

回帰テストでは、カタログに記載されたすべての定理が `Proven` として正しく登録されることを確認します。前提として許可される語彙は指定の公理一覧に限定され、証明ファイル側での公理追加は禁止されます。また、定義への依存を保った宣言順で再検証し、証明を持つ宣言では前提追加を禁止して（`--no-axioms` 同等）、誤った結論や不正な証明項が適切に拒否されることを確認しています。

## ラッセルの議論と普遍集合

[Web用の証明](../examples/commons/sets/russell.ht)は、すべての集合を含む集合 `u` があると仮定し、分出で `r = {x ∈ u | x ∉ x}` を作ります。`r ∈ r` なら分出の条件から `r ∉ r` が得られるため、まず `r ∉ r` を証明できます。一方、普遍集合の仮定から `r ∈ u` なので、分出の逆向きの条件から `r ∈ r` が得られ、矛盾します。最終定理 `no_universal_set` は `¬∃u, ∀x, x ∈ u` を表します。

前提は既存の論理・量化規則に加え、[集合の所属関係と分出](../examples/commons/foundation/sets.ht)です。分出は既存の集合の部分集合を作る規則で、任意の性質から無制限に集合を作る内包原理ではありません。このデモでは述語パラメータで分出の図式を表し、排中律・選択公理・普遍集合の非存在そのものは仮定しません。

[既存のRocq/ZFC検証](../rocq/zfc/README.md)と同じラッセルの議論を、Webで読みやすい名前付きの証明項として別途記述しています。このWeb例はproofglyphのOCamlカーネルとブラウザ用検査器で検査しますが、Rocq側の一階論理AST・符号化との対応は証明していません。既存のRocq検証の対象は従来の証明項です。
