# 証明カタログ

`examples/commons/` には、論理・等式・自然数・整数論などの規則・定義・定理を分野別のモジュールとして収録しています。算術の土台は Peano 公理、論理・等式の推論規則、および明示的な述語と再帰方程式の定義に限定し、すべての定理はこれらから導出された証明項として記述されています。

- [命題論理](../examples/commons/logic/propositional.tp): 含意、連言、選言、対偶、構成的なド・モルガン則。古典論理と量化は別モジュール。
- [等式](../examples/commons/equality.tp): 固定した型 `U` 上の反射律と置換から導出する3定理。
- [ライブラリの構成](../examples/commons/README.md): 加算、乗算、順序、整除性、合同式、素数、有限和など、用途に応じたモジュール。
- [Peano の土台](../examples/commons/foundation/peano.tp): 自然数の記号、等式、帰納法、後者関数の単射性と0との区別。
- [フェルマーの利用例](../examples/fermat_application.tp): 証明済みの小定理を import し、和に適用する定理。

`examples/commons/foundation/` は前提となる語彙・公理・定義を含み、`examples/commons/logic/`、`examples/commons/equality.tp`、`examples/commons/nat/` はそれらに基づいて型検査される証明項です。証明ファイル自体には `axiom` を含みません。定義済みおよび証明済みの定数は不透明（opaque）として扱われ、定義や証明の本体は展開されません。そのため、項の計算や式の変形には等式の証明項を用います。

## 実装した証明

式中の `A → B` は証明の関数型 `Prf A -> Prf B`、`¬A` は `Not A` を表します。各宣言名のリンクから、個々の証明項と依存関係を参照できます。

| 分野 | 命題・操作 | 宣言名 | ファイル |
| --- | --- | --- | --- |
| 入門 | 恒等関数・依存型・β同値 | [id](../examples/basics.tp), [dependent_id](../examples/basics.tp), [beta](../examples/basics.tp) | `basics.tp` |
| 入門 | 証明済みの含意の合成を使う | [composition_example](../examples/logic.tp) | `logic.tp` |
| 論理 | 含意の合成 `(A → B) → (B → C) → A → C` | [implication_composition](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 引数の交換・複製、関数の合成 | [exchange](../examples/commons/logic/propositional.tp), [duplicate](../examples/commons/logic/propositional.tp), [function_composition](../examples/commons/logic/quantifiers.tp) | `logic/propositional.tp`, `logic/quantifiers.tp` |
| 論理 | 連言の交換則・結合則（両方向） | [and_comm](../examples/commons/logic/propositional.tp), [and_assoc_forward](../examples/commons/logic/propositional.tp), [and_assoc_backward](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 選言の交換則・場合分け | [or_comm](../examples/commons/logic/propositional.tp), [cases](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | 対偶 `(A → B) → (¬B → ¬A)` | [contraposition](../examples/commons/logic/propositional.tp) | `logic/propositional.tp` |
| 論理 | ド・モルガン則 `¬(A ∨ B) ⇔ (¬A ∧ ¬B)`、`¬(A ∧ B) ⇔ (¬A ∨ ¬B)` | [demorgan_or_forward](../examples/commons/logic/demorgan.tp), [demorgan_or_backward](../examples/commons/logic/demorgan.tp), [demorgan_and_forward](../examples/commons/logic/demorgan.tp), [demorgan_and_backward](../examples/commons/logic/demorgan.tp) | `logic/demorgan.tp` |
| 論理 | 全称の具体化・存在への証人導入 | [forall_specialize](../examples/commons/logic/quantifiers.tp), [exists_witness](../examples/commons/logic/quantifiers.tp), [forall_to_exists](../examples/commons/logic/quantifiers.tp) | `logic/quantifiers.tp` |
| 等式 | 対称律・推移律・関数による保存 | [eq_sym](../examples/commons/equality.tp), [eq_trans](../examples/commons/equality.tp), [eq_cong](../examples/commons/equality.tp) | `equality.tp` |
| 自然数 | 強い帰納法 | [nat_strong_induction](../examples/commons/nat/induction.tp) | `nat/induction.tp` |
| 自然数 | `0 + n = n`, `n + 0 = n` | [add_zero_left](../examples/commons/nat/addition.tp), [add_zero_right](../examples/commons/nat/addition.tp) | `nat/addition.tp` |
| 自然数 | 加算の結合則・交換則 | [add_assoc](../examples/commons/nat/addition.tp), [add_comm](../examples/commons/nat/addition.tp) | `nat/addition.tp` |
| 自然数 | 乗算の分配則（両側）・結合則・交換則 | [mul_add_left](../examples/commons/nat/multiplication.tp), [mul_add_right](../examples/commons/nat/multiplication.tp), [mul_assoc](../examples/commons/nat/multiplication.tp), [mul_comm](../examples/commons/nat/multiplication.tp) | `nat/multiplication.tp` |
| 自然数 | `a^(m+n) = a^m a^n` | [pow_add](../examples/commons/nat/powers.tp) | `nat/powers.tp` |
| 自然数 | 偶数同士・奇数同士の和は偶数 | [even_add](../examples/commons/nat/parity.tp), [odd_add](../examples/commons/nat/parity.tp) | `nat/parity.tp` |
| 自然数 | `2Σ(k=1..n) k = n(n+1)` | [triangular_double](../examples/commons/nat/sums.tp) | `nat/sums.tp` |
| 整数論 | 整除性の推移律・和・積への保存 | [divides_trans](../examples/commons/nat/divisibility.tp), [divides_add](../examples/commons/nat/divisibility.tp), [divides_mul_right](../examples/commons/nat/divisibility.tp), [divides_mul_left](../examples/commons/nat/divisibility.tp) | `nat/divisibility.tp` |
| 整数論 | 合同式の加算・乗算・累乗による保存 | [cong_add](../examples/commons/nat/congruence.tp), [cong_mul](../examples/commons/nat/congruence.tp), [cong_pow](../examples/commons/nat/congruence.tp) | `nat/congruence.tp` |
| 整数論 | 除法の原理（商と余りの存在） | [division_algorithm](../examples/commons/nat/division.tp) | `nat/division.tp` |
| 整数論 | 最小の正の証人の存在 | [least_positive](../examples/commons/nat/division.tp) | `nat/division.tp` |
| 整数論 | 素因数の存在 | [prime_factor](../examples/commons/nat/factorization.tp) | `nat/factorization.tp` |
| 整数論 | ユークリッドの補題・平方の整除性 | [prime_mul_elim](../examples/commons/nat/euclid.tp), [prime_divides_square](../examples/commons/nat/euclid.tp) | `nat/euclid.tp` |
| 整数論 | 素数 `p` は `C(p,k)` を割り切る（`0 < k < p`） | [prime_divides_choose](../examples/commons/nat/prime_binomial.tp) | `nat/prime_binomial.tp` |
| 整数論 | 二項定理 | [binomial_theorem](../examples/commons/nat/binomial_theorem.tp) | `nat/binomial_theorem.tp` |
| 整数論 | 素数は無限に存在する | [primes_infinite](../examples/commons/nat/prime_infinitude.tp) | `nat/prime_infinitude.tp` |
| 整数論 | √2 の無理性 | [sqrt_two_coprime_contradiction](../examples/commons/nat/sqrt_two.tp), [sqrt_two_irrational](../examples/commons/nat/sqrt_two.tp) | `nat/sqrt_two.tp` |
| 整数論 | フェルマーの小定理と和への適用 | [fermat](../examples/commons/nat/fermat.tp), [fermat_sum](../examples/commons/nat/fermat.tp) | `nat/fermat.tp` |

なお、`function_composition` は `f, g : U -> U` と `x : U` から合成関数 `g (f x) : U` を構築するプログラム項であり、命題の証明項ではありません。

## axiom の位置づけ

ソースコード中の `axiom` は、不透明な記号や推論規則をシグネチャに登録する構文です。本ライブラリでは任意の補題を公理として仮定することはせず、以下の4種類に限定して使用しています。定義の自動展開を行わない LF の性質上、述語の定義規則や再帰方程式も `axiom` 構文で明示します。

| 種類 | 内容 |
| --- | --- |
| 語彙 | `Nat`, `zero`, `succ`, `Prop`, `Prf`, `Eq`、演算・述語の型 |
| Peano と等式 | `nat_induction`, `succ_injective`, `succ_not_zero`, `eq_refl`, `eq_subst` |
| 論理 | 連言・選言・偽・否定・含意・量化の導入／除去、古典論理の排中律 |
| 定義 | 述語の導入／除去、加算などの再帰方程式、有限和による `convolution` の定義 |

たとえば `prime_intro` / `prime_elim` は、素数を「1より大きく、各約数が1または自分自身である数」と定義します（ユークリッドの補題は公理ではなく定理として証明します）。また `coprime_intro` / `coprime_elim` は、共通の約数が1のみであることを定義します。

`proven` は、明示したシグネチャの下で証明項の型検査に成功した状態を表します。Peano の構成や定義方程式はシグネチャとして外部から与えられており、Kernel の内部に特定の算術論理や簡約規則は組み込まれていません。

自然数ライブラリには135個の `theorem` が含まれます。読み込まれる `axiom` は利用するモジュールに応じて決定され、Peano 公理に加えて演算や述語の語彙、論理規則、再帰方程式などが含まれます。

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

加算・乗算の結合則や交換則、累乗の加法則、三角数の公式などは帰納法から導出されます。[強い帰納法](../examples/commons/nat/induction.tp) も、通常の Peano 帰納法と順序の定義から導出される定理です。

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

[素因数の存在](../examples/commons/nat/factorization.tp) は、1 より大きい数が素数ならその数自身を取り、素数でなければ真の約数へ強い帰納法で降下します。真の約数の存在は素数の定義と古典論理から導出されます。

[除法の原理](../examples/commons/nat/division.tp) は、正の除数 `d` に対して `n = d * q + r`（`r < d`）を満たす `q, r` を強い帰納法で構成します。

[ユークリッドの補題](../examples/commons/nat/euclid.tp) は、`p | a * t` を満たす最小の正の `t` を取り、除法の原理と最小性から `t` が `p` と `b` を割り切ることを示します。素数の定義による `t = 1` または `t = p` の場合分けから `p | a` または `p | b` を導きます。

[素数の無限性](../examples/commons/nat/prime_infinitude.tp) は `n! + 1` の素因数を取ります。もしそれが `n` 以下であれば、階乗と `n! + 1` の両方を割り切るため 1 を割り切ることになり矛盾します。

### 二項係数と有限和

二項係数の定義は、境界値とパスカルの再帰方程式です。

```text
choose n zero = 1
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n k + choose n (succ k)
```

[係数の恒等式](../examples/commons/nat/binomial_coefficients.tp) は、先に `choose_balance` で `(k+1)*C(n+1,k+1)=(n+1)*C(n,k)` を帰納法で証明し、正の添字を後者の形に移します。ユークリッドの補題と素数の整除性から `prime_divides_choose` を導出します。

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

[二項定理](../examples/commons/nat/binomial_theorem.tp) はこれらの補題、累乗の再帰、分配則から `n` の帰納法で証明します。開区間の和の合同保存も、その和の再帰定義と順序の比較から帰納法で証明します。

### √2 の無理性

[sqrt_two_no_positive_fraction](../examples/commons/nat/sqrt_two.tp) は、任意の自然数 `a, b` に対して `b > 0` と `a * a = 2 * (b * b)` から矛盾を導きます。既約分数への変換や互いに素であることを仮定しません。

ユークリッドの補題と 2 の素数性から `a` と `b` がともに 2 の倍数であることを示し、`a = 2k`, `b = 2j` と置きます。2 を消去すると `k * k = 2 * (j * j)` となり、`0 < j < b` であるため分母に関する強い帰納法により矛盾が導かれます。`sqrt_two_irrational` はこの定理から有理数表示の存在を排除します。

### 論理と古典性

論理・等式のモジュールも基本規則から導出されます。論理の量化は固定した型 `U` 上、算術の量化は `Nat` 上で行い、有限和の証明には自然数値の関数を量化する規則も用います。

ド・モルガン則のうち `¬(A ∧ B) → ¬A ∨ ¬B` の証明には排中律を用います（他の3方向および対偶は直観主義論理の範囲で構成的です）。算術ライブラリにおいても、素因数の存在、最小の正の証人、ユークリッドの補題などの一部の定理では古典論理を用いて証明しています。

## フェルマーの小定理

[fermat](../examples/commons/nat/fermat.tp) は、以下の順で証明します。

1. `prime_divides_choose` から、二項展開の内側の各項が 0 と合同になる。
2. `sum_between_cong_zero` で内側の和も 0 と合同になる。
3. `binomial_theorem` と証明済みの両端分離から、`(x+1)^p ≡ x^p+1 (mod p)` を得る。
4. 帰納法の仮定 `x^p ≡ x` を使い、後者の式へ移す。
5. 素数の正値性と `pow_zero_positive` を基底として、自然数の帰納法を適用する。

[fermat_sum](../examples/commons/nat/fermat.tp) は、証明済みの小定理に `x = a + b` を代入します。利用例の `fermat_application` はこの定理を import して適用します。

## 検証

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/commons/nat/fermat.tp -o /tmp/fermat.pa
dune exec bin/main.exe -- check /tmp/fermat.pa
# 分野別モジュールを単独で検査できる
dune exec bin/main.exe -- compile examples/commons/nat/euclid.tp -o /tmp/euclid.pa
dune exec bin/main.exe -- check /tmp/euclid.pa
```

回帰テストでは、カタログに記載されたすべての定理が `Proven` として正しく登録されることを確認します。前提として許可される語彙は指定の公理一覧に限定され、証明ファイル側での公理追加は禁止されます。また、前提を先頭に集めたシグネチャに対して証明部分を前提追加禁止（`--no-axioms` 同等）で再検証し、誤った結論や不正な証明項が適切に拒否されることを確認しています。
