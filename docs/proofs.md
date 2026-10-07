# 証明カタログ

関連する規則・定義・定理を `examples/commons/` の分野別モジュールにまとめ、必要なモジュールを `import` する。従来の未証明補題は証明項に置き換え、算術の土台は Peano 公理、論理・等式の規則、明示した述語と再帰関数の定義に限定する。

- [命題論理](../examples/commons/logic/propositional.tp): 含意、連言、選言、対偶、構成的なド・モルガン則。古典論理と量化は別モジュール。
- [等式](../examples/commons/equality.tp): 固定した型 `U` 上の反射律と置換から導出する3定理。
- [ライブラリの構成](../examples/commons/README.md): 加算、乗算、順序、整除性、合同式、素数、有限和など、用途に応じたモジュール。
- [Peano の土台](../examples/commons/foundation/peano.tp): 自然数の記号、等式、帰納法、後者関数の単射性と0との区別。
- [フェルマーの利用例](../examples/fermat_application.tp): 証明済みの小定理を import し、和に適用する定理。

`examples/commons/foundation/` は信頼する語彙・規則・定義、`examples/commons/logic/`・`examples/commons/equality.tp`・`examples/commons/nat/` は検査する証明項である。証明ファイルに `axiom` はない。Kernel の規則は変更していない。定義済み・証明済みの定数は不透明なままであり、計算や変形には等式の証明を使う。

## 実装した証明

式中の `A → B` は証明の関数型 `Prf A -> Prf B`、`¬A` は `Not A` として表す。各宣言名のリンクで、個々の証明と import の依存先を読める。

| 分野 | 命題・操作 | 宣言名 | ファイル |
| --- | --- | --- | --- |
| 論理 | 含意の合成 `(A → B) → (B → C) → A → C` | [implication_composition](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 引数の交換・複製、関数の合成 | [exchange](../examples/commons/logic/propositional.tp), [duplicate](../examples/commons/logic/propositional.tp), [function_composition](../examples/commons/logic/quantifiers.tp) | `logic/propositional.tp`, `logic/quantifiers.tp` |
| 論理 | 連言の交換則・結合則（両方向） | [and_comm](../examples/commons/logic/propositional.tp), [and_assoc_forward](../examples/commons/logic/propositional.tp), [and_assoc_backward](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 選言の交換則・場合分け | [or_comm](../examples/commons/logic/propositional.tp), [cases](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 対偶 `(A → B) → (¬B → ¬A)` | [contraposition](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | ド・モルガン則（4方向） | [demorgan_or_forward](../examples/commons/logic/propositional.tp), [demorgan_or_backward](../examples/commons/logic/propositional.tp), [demorgan_and_forward](../examples/commons/logic/classical.tp), [demorgan_and_backward](../examples/commons/logic/propositional.tp) | `logic/propositional.tp`, `logic/classical.tp` |
| 論理 | 全称の具体化・存在への証人導入 | [forall_specialize](../examples/commons/logic/quantifiers.tp), [exists_witness](../examples/commons/logic/quantifiers.tp), [forall_to_exists](../examples/commons/logic/quantifiers.tp) | `logic/quantifiers.tp` |
| 等式 | 対称律・推移律・関数による保存 | [eq_sym](../examples/commons/equality.tp), [eq_trans](../examples/commons/equality.tp), [eq_cong](../examples/commons/equality.tp) | `equality.tp` |
| 自然数 | `0 + n = n`, `n + 0 = n` | [add_zero_left](../examples/commons/nat/addition.tp), [add_zero_right](../examples/commons/nat/addition.tp) | `nat/addition.tp` |
| 自然数 | 加算の結合則・交換則 | [add_assoc](../examples/commons/nat/addition.tp), [add_comm](../examples/commons/nat/addition.tp) | `nat/addition.tp` |
| 自然数 | 乗算の分配則（両側）・結合則・交換則 | [mul_add_left](../examples/commons/nat/multiplication.tp), [mul_add_right](../examples/commons/nat/multiplication.tp), [mul_assoc](../examples/commons/nat/multiplication.tp), [mul_comm](../examples/commons/nat/multiplication.tp) | `nat/multiplication.tp` |
| 自然数 | `a^(m+n) = a^m a^n` | [pow_add](../examples/commons/nat/powers.tp) | `nat/powers.tp` |
| 自然数 | 偶数同士・奇数同士の和は偶数 | [even_add](../examples/commons/nat/parity.tp), [odd_add](../examples/commons/nat/parity.tp) | `nat/parity.tp` |
| 自然数 | `2Σ(k=1..n) k = n(n+1)` | [triangular_double](../examples/commons/nat/sums.tp) | `nat/sums.tp` |
| 整数論 | 整除性の推移律・和・積への保存 | [divides_trans](../examples/commons/nat/divisibility.tp), [divides_add](../examples/commons/nat/divisibility.tp), [divides_mul_right](../examples/commons/nat/divisibility.tp), [divides_mul_left](../examples/commons/nat/divisibility.tp) | `nat/divisibility.tp` |
| 整数論 | 合同式の加算・乗算・累乗による保存 | [cong_add](../examples/commons/nat/congruence.tp), [cong_mul](../examples/commons/nat/congruence.tp), [cong_pow](../examples/commons/nat/congruence.tp) | `nat/congruence.tp` |
| 整数論 | 素数 `p` は `C(p,k)` を割り切る（`0 < k < p`） | [prime_divides_choose](../examples/commons/nat/prime_binomial.tp) | `nat/prime_binomial.tp` |
| 整数論 | 二項定理 | [binomial_theorem](../examples/commons/nat/binomial_theorem.tp) | `nat/binomial_theorem.tp` |
| 整数論 | 素数は無限に存在する | [primes_infinite](../examples/commons/nat/prime_infinitude.tp) | `nat/prime_infinitude.tp` |
| 整数論 | √2 の無理性 | [sqrt_two_coprime_contradiction](../examples/commons/nat/sqrt_two.tp), [sqrt_two_irrational](../examples/commons/nat/sqrt_two.tp) | `nat/sqrt_two.tp` |
| 整数論 | フェルマーの小定理と和への適用 | [fermat](../examples/commons/nat/fermat.tp), [fermat_sum](../examples/commons/nat/fermat.tp) | `nat/fermat.tp` |

`function_composition` は `f, g : U -> U` と `x : U` から `g (f x) : U` を構成する項であり、命題の証明ではない。

## 残る axiom の意味

ソースの `axiom` は、不透明な記号・規則を署名に登録する構文である。次の4種類を区別する。数学的な補題を仮定する宣言は残していないが、定義を自動展開しない LF のため、定義の規則・方程式も `axiom` 構文で明示する。

| 種類 | 内容 |
| --- | --- |
| 語彙 | `Nat`, `zero`, `succ`, `Prop`, `Prf`, `Eq`、演算・述語の型 |
| Peano と等式 | `nat_induction`, `succ_injective`, `succ_not_zero`, `eq_refl`, `eq_subst` |
| 論理 | 連言・選言・偽・否定・含意・量化の導入／除去、古典論理の排中律 |
| 定義 | 述語の導入／除去、加算などの再帰方程式、有限和による `convolution` の定義 |

たとえば `prime_intro` / `prime_elim` は、素数を「1より大きく、各約数が1または自分自身である数」と定義する。ユークリッドの補題をその規則に含めない。`coprime_intro` / `coprime_elim` は、共通の約数がすべて1であることを定義する。公理に残っていた `prime_mul_elim` と `coprime_no_common_prime` は、これらの定義から導出した定理である。

`proven` は、この明示した署名の下で証明項の型検査に成功したことを意味する。Kernel が公理・定義の標準的な数学的意味や、理論の無矛盾性を検証するわけではない。Peano の構成と定義方程式は署名に明示しており、Kernel 内に算術や書換え規則を組み込まない。

自然数ライブラリには135個の `theorem` がある。読み込まれる `axiom` の数は利用するモジュールに依存する。演算・述語の語彙、論理規則、述語の定義、再帰方程式を含むため、Peano 公理だけの数ではない。従来の補題・数値等式23宣言はすべて定理へ置き換えた。

### 自然数と再帰関数

1は `succ zero`、2は `succ (succ zero)` と書く。不透明な数値定数や、それを値に結び付ける公理は使わない。`one_succ` / `two_succ` は現在は反射律の定理である。

加算・乗算・累乗は次の再帰方程式を定義として持つ。`pred`、`factorial`、`triangular` も同様に、0と後者の場合を分けて定義する。

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

加算・乗算の法則、累乗の加法則、三角数の公式、乗算の消去は帰納法で導出する。[強い帰納法](../examples/commons/nat/induction.tp) も、通常の Peano の帰納法と順序の定義から証明する。追加の帰納原理として仮定しない。

### 述語の定義

導入・除去規則は、次の存在・全称による定義を表す。

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

合同式は自然数の切り捨て減算を避けるため、両側に倍数を足す定義を使う。整除性・合同式の推移律、演算による保存、整除性の加算からの消去は、証人と算術の等式を構成して証明する。整数型や実数型は導入していない。

### 素因数、ユークリッドの補題、無限性

[素因数の存在](../examples/commons/nat/factorization.tp) は、1より大きい数が素数ならその数自身を取り、素数でなければ真の約数へ強い帰納法で降りる。真の約数の存在は素数の定義と古典論理から導出する。

[除法の原理](../examples/commons/nat/division.tp) は、正の除数 `d` に対して `n=d*q+r`, `r<d` を満たす `q,r` を強い帰納法で構成する。

[ユークリッドの補題](../examples/commons/nat/euclid.tp) は、`p|a*t` を満たす最小の正の `t` を取る。除法の原理と最小性から、この `t` が `p` と `b` を割り切ることを示す。素数の定義による `t=1` または `t=p` の場合分けから、`p|a` または `p|b` を得る。

[素数の無限性](../examples/commons/nat/prime_infinitude.tp) は `n!+1` の素因数を取る。もしそれが `n` 以下なら、階乗と `n!+1` の両方を割り切るので1も割り切るという矛盾になる。階乗の正値性・整除性、素数は1を割り切らないことも証明済みである。

### 二項係数と有限和

二項係数の定義は、境界値とパスカルの再帰方程式である。

```text
choose n zero = 1
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n k + choose n (succ k)
```

[係数の恒等式](../examples/commons/nat/binomial_coefficients.tp) は、先に `choose_balance` で `(k+1)*C(n+1,k+1)=(n+1)*C(n,k)` を帰納法で証明し、正の添字を後者の形に移す。ユークリッドの補題と素数の整除性から `prime_divides_choose` を導出する。

有限和には、通常の接頭和 `sum`、開区間の和 `sum_between`、`i+j=n` の対角線上の和 `diagonal` を定義する。対角和は次の再帰方程式を持つ。

```text
diagonal zero h = h zero zero
diagonal (succ n) h
  = diagonal n (i,j ↦ h i (succ j)) + h (succ n) zero
```

`convolution` は、この対角和を使った明示的な定義である。

```text
convolution n f g = diagonal n (i,j ↦ C(n,i)*f(i)*g(j))
                 = Σ(i+j=n) C(n,i)*f(i)*g(j)
```

パスカルの関係式に対応する `convolution_pascal`、基底の `convolution_zero`、外延性、係数の取り出し、両端の分離はすべて定理である。パスカルの式を `convolution` の公理として残さず、二項係数の再帰と対角和の加法・添字の移動から導出する。

[二項定理](../examples/commons/nat/binomial_theorem.tp) はこれらの補題、累乗の再帰、分配則から `n` の帰納法で証明する。開区間の和の合同保存も、その和の再帰定義と順序の比較から帰納法で証明する。

### √2 の無理性

[sqrt_two_no_positive_fraction](../examples/commons/nat/sqrt_two.tp) は、任意の自然数 `a,b` に対して `b>0` と `a*a=2*(b*b)` から矛盾を導く。既約分数への変換や互いに素であることを仮定しない。

ユークリッドの補題と2の素数性から `a` と `b` がともに2の倍数であることを示し、`a=2k`, `b=2j` を取る。2を消去すると `k*k=2*(j*j)` となり、`0<j<b` なので分母についての強い帰納法で矛盾する。`sqrt_two_irrational` は有理数表示の存在をこの定理で排除する。実数の平方根や有理数型自体の構築は、この算術的な表現とは別である。

### 論理と古典性

論理・等式のカタログも基本規則から導出する。論理の量化は固定した型 `U` 上、算術の量化は `Nat` 上、有限和の証明には自然数値の関数を量化する論理規則も使う。

ド・モルガン則の `¬(A ∧ B) → ¬A ∨ ¬B` は排中律を使う。残る3方向と対偶は構成的である。算術では素因数・最小の正の証人・ユークリッドの補題などの証明に古典論理を使う。すべての証明が構成的という主張はしない。

## フェルマーの小定理

[fermat](../examples/commons/nat/fermat.tp) は、以下の順で証明する。

1. `prime_divides_choose` から、二項展開の内側の各項が0と合同になる。
2. `sum_between_cong_zero` で内側の和も0と合同になる。
3. `binomial_theorem` と証明済みの両端分離から、`(x+1)^p ≡ x^p+1 (mod p)` を得る。
4. 帰納法の仮定 `x^p ≡ x` を使い、後者の式へ移す。
5. 素数の正値性と `pow_zero_positive` を基底として、自然数の帰納法を適用する。

[fermat_sum](../examples/commons/nat/fermat.tp) は、証明済みの小定理に `x=a+b` を代入する。利用例の `fermat_application` はこの定理を import して適用する。

## 検証

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/commons/nat/fermat.tp -o /tmp/fermat.pa
dune exec bin/main.exe -- check /tmp/fermat.pa
# 分野別モジュールを単独で検査できる。
dune exec bin/main.exe -- compile examples/commons/nat/euclid.tp -o /tmp/euclid.pa
dune exec bin/main.exe -- check /tmp/euclid.pa
```

回帰テストは、各候補と旧補題のすべてが `Proven` として登録されることを確認する。前提の語彙は固定した許可一覧に限定し、証明ファイルからの公理追加を許さない。固定前提を先頭に集めた署名でも再コンパイルし、証明部分を前提追加禁止で再検証する。誤った結論、合同式の法、添字の条件、存在の証人、平方根の方程式、分母の正値性を使った証明は拒否する。

これらは実装と証明項の検査であり、Kernel 自体の形式的な健全性証明ではない。
