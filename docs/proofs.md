# Proof catalog

`examples/commons/` groups rules, definitions, and theorems in logic, equality, natural numbers, and number theory into subject modules. Arithmetic rests on Peano axioms, logical/equality rules, primitive-recursion axioms, and explicit predicate/operation definitions. Every theorem is written as a proof term derived from these foundations.

- [Propositional logic](../examples/commons/logic/propositional.ht): implication, conjunction, disjunction, contraposition, constructive De Morgan laws. Classical logic and quantification are separate modules.
- [No universal set](../examples/commons/sets/russell.ht): Russell's argument from separation and logical rules.
- [Equality](../examples/commons/equality.ht): three theorems derived from reflexivity and substitution over a fixed type `U`.
- [Library structure](../examples/commons/README.md): modules for addition, multiplication, order, divisibility, congruence, primes, finite sums, and more.
- [Peano foundations](../examples/commons/foundation/peano.ht): natural-number symbols, equality, induction, successor injectivity, and distinction from zero.
- [Applying Fermat](../examples/fermat_application.ht): import the proved little theorem and apply it to a sum.

`examples/commons/foundation/` contains vocabulary, axioms, and definitions. `examples/commons/logic/`, `examples/commons/equality.ht`, `examples/commons/nat/`, and `examples/commons/sets/` contain proof terms checked against them. Proof files themselves contain no `axiom` declarations. Hieratic expands `def` bodies at compile time; `theorem` retains opaque references. The kernel uses β equivalence, while recursive arithmetic computations use proof terms for the corresponding equations.

## Implemented proofs

In formulas, `A → B` means the proof-function type `Prf A -> Prf B`, and `¬A` means `Not A`. Declaration links lead to individual proof terms and dependencies.

<!-- proof-catalog:start -->

| Subject | Proposition / operation | Declaration | File |
| --- | --- | --- | --- |
| Introduction | Identity, dependent types, β equivalence | [id](../examples/basics.ht), [dependent_id](../examples/basics.ht), [beta](../examples/basics.ht) | `basics.ht` |
| Introduction | Using proved implication composition | [composition_example](../examples/logic.ht) | `logic.ht` |
| Logic | Implication composition `(A → B) → (B → C) → A → C` | [implication_composition](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| Logic | Argument exchange/duplication and function composition | [exchange](../examples/commons/logic/propositional.ht), [duplicate](../examples/commons/logic/propositional.ht), [function_composition](../examples/commons/logic/quantifiers.ht) | `logic/propositional.ht`, `logic/quantifiers.ht` |
| Logic | Conjunction commutativity and associativity (both directions) | [and_comm](../examples/commons/logic/propositional.ht), [and_assoc_forward](../examples/commons/logic/propositional.ht), [and_assoc_backward](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| Logic | Disjunction commutativity and case analysis | [or_comm](../examples/commons/logic/propositional.ht), [cases](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| Logic | Contraposition `(A → B) → (¬B → ¬A)` | [contraposition](../examples/commons/logic/propositional.ht) | `logic/propositional.ht` |
| Logic | De Morgan laws `¬(A ∨ B) ⇔ (¬A ∧ ¬B)`, `¬(A ∧ B) ⇔ (¬A ∨ ¬B)` | [demorgan_or_forward](../examples/commons/logic/demorgan.ht), [demorgan_or_backward](../examples/commons/logic/demorgan.ht), [demorgan_and_forward](../examples/commons/logic/demorgan.ht), [demorgan_and_backward](../examples/commons/logic/demorgan.ht) | `logic/demorgan.ht` |
| Logic | Universal specialization and existential witnesses | [forall_specialize](../examples/commons/logic/quantifiers.ht), [exists_witness](../examples/commons/logic/quantifiers.ht), [forall_to_exists](../examples/commons/logic/quantifiers.ht) | `logic/quantifiers.ht` |
| Equality | Symmetry, transitivity, and function congruence | [eq_sym](../examples/commons/equality.ht), [eq_trans](../examples/commons/equality.ht), [eq_cong](../examples/commons/equality.ht) | `equality.ht` |
| Natural numbers | Strong induction | [nat_strong_induction](../examples/commons/nat/induction.ht) | `nat/induction.ht` |
| Natural numbers | `0 + n = n`, `n + 0 = n` | [add_zero_left](../examples/commons/nat/addition.ht), [add_zero_right](../examples/commons/nat/addition.ht) | `nat/addition.ht` |
| Natural numbers | Addition associativity and commutativity | [add_assoc](../examples/commons/nat/addition.ht), [add_comm](../examples/commons/nat/addition.ht) | `nat/addition.ht` |
| Natural numbers | Multiplication distributivity (both sides), associativity, and commutativity | [mul_add_left](../examples/commons/nat/multiplication.ht), [mul_add_right](../examples/commons/nat/multiplication.ht), [mul_assoc](../examples/commons/nat/multiplication.ht), [mul_comm](../examples/commons/nat/multiplication.ht) | `nat/multiplication.ht` |
| Natural numbers | `a^(m+n) = a^m a^n` | [pow_add](../examples/commons/nat/powers.ht) | `nat/powers.ht` |
| Natural numbers | Sums of two even or two odd numbers are even | [even_add](../examples/commons/nat/parity.ht), [odd_add](../examples/commons/nat/parity.ht) | `nat/parity.ht` |
| Natural numbers | `2Σ(k=1..n) k = n(n+1)` | [triangular_double](../examples/commons/nat/sums.ht) | `nat/sums.ht` |
| Natural numbers | `1 + 3 + … + (2n−1) = n²` | [odd_sum_square](../examples/commons/nat/sums.ht) | `nat/sums.ht` |
| Number theory | Divisibility transitivity and preservation under sums/products | [divides_trans](../examples/commons/nat/divisibility.ht), [divides_add](../examples/commons/nat/divisibility.ht), [divides_mul_right](../examples/commons/nat/divisibility.ht), [divides_mul_left](../examples/commons/nat/divisibility.ht) | `nat/divisibility.ht` |
| Number theory | Congruence preservation under addition, multiplication, and powers | [cong_add](../examples/commons/nat/congruence.ht), [cong_mul](../examples/commons/nat/congruence.ht), [cong_pow](../examples/commons/nat/congruence.ht) | `nat/congruence.ht` |
| Number theory | Division algorithm (existence of quotient and remainder) | [division_algorithm](../examples/commons/nat/division.ht) | `nat/division.ht` |
| Number theory | Existence of prime factors | [prime_factor](../examples/commons/nat/factorization.ht) | `nat/factorization.ht` |
| Number theory | Euclid's lemma and divisibility of squares | [prime_mul_elim](../examples/commons/nat/euclid.ht), [prime_divides_square](../examples/commons/nat/euclid.ht) | `nat/euclid.ht` |
| Number theory | A prime `p` divides `C(p,k)` for `0 < k < p` | [prime_divides_choose](../examples/commons/nat/prime_binomial.ht) | `nat/prime_binomial.ht` |
| Number theory | Binomial theorem | [binomial_theorem](../examples/commons/nat/binomial_theorem.ht) | `nat/binomial_theorem.ht` |
| Number theory | Infinitely many primes | [primes_infinite](../examples/commons/nat/prime_infinitude.ht) | `nat/prime_infinitude.ht` |
| Number theory | Irrationality of √2 | [sqrt_two_coprime_contradiction](../examples/commons/nat/sqrt_two.ht), [sqrt_two_irrational](../examples/commons/nat/sqrt_two.ht) | `nat/sqrt_two.ht` |
| Number theory | Fermat's little theorem and application to sums | [fermat](../examples/commons/nat/fermat.ht), [fermat_sum](../examples/commons/nat/fermat.ht) | `nat/fermat.ht` |
| Set theory | No universal set via Russell's paradox | [no_universal_set](../examples/commons/sets/russell.ht) | `sets/russell.ht` |

<!-- proof-catalog:end -->

`function_composition` constructs the program term `g (f x) : U` from `f, g : U -> U` and `x : U`; it is not a propositional proof term.

## Role of axioms

`symbol` declares undefined types/symbols, `axiom` trusted principles, `def` definitions with bodies, and `theorem` theorems with proof terms. Both `symbol` and `axiom` count as kernel assumptions; renaming alone does not reduce the trusted basis.

| Kind | Declarations and contents |
| --- | --- |
| Vocabulary | `symbol`: `Nat`, `zero`, `succ`, `Prop`, `Prf`, `Eq`, logical symbols, and recursors |
| Peano and equality | `axiom`: `nat_induction`, `succ_not_zero`, `eq_subst` (Nat / U), `eq_refl` (U only) |
| Logic | `axiom`: basic implication/universal-quantification rules and excluded middle |
| Recursion | `axiom`: base/successor rules for primitive recursion at function types |
| Sets | `symbol Mem` and `axiom separation`: separation forming subsets of existing sets |
| Definitions and derivations | `def`: predicates such as `Divides`, `Prime`, and operations. `theorem`: their introduction/elimination rules and recursive equations |

`And`, `Or`, and `False` use Church encodings with implication and quantification over propositions. `Not A` is `Imp A False`; `Exists` is defined using universal quantification and implication. Their introduction/elimination rules are checked as `theorem`. `succ_injective` is proved from a left inverse supplied by the recursor, rather than assumed. Natural-number `eq_refl` is also proved from the recursion base equation and substitution. Quantification over propositions is a newly stated principle; it is not claimed to follow from the earlier axioms.

For example, `Divides d a` is `Exists (fun (k : Nat) => Eq a (mul d k))`; `divides_intro` / `divides_elim` follow from existential rules. `Prime p` means a number greater than 1 whose divisors are 1 or itself; `prime_intro` / `prime_elim` follow from conjunction, implication, and quantification rules.

Across foundation files, unproved rules/axioms were reduced from 75 declarations to 17, and kernel assumptions including vocabulary from 116 to 31. These totals include same-named equality/quantification declarations over different domains. Each proof loads only its required modules.

`Proven` denotes a proof term type-checked under the stated assumptions. Recursion principles are among those assumptions, so existence of recursors is not claimed to follow from Peano axioms alone. The new definition expansion itself is outside the existing Rocq frontend proofs described here, but output is independently rechecked by the extracted checker.

Quantification over naturals (`AllNat`) and sequences (`AllSeq`) is defined from quantification over binary natural-number functions (`AllBi`). Their introduction/elimination rules use evaluation at zero and embedding into constant functions. No new quantification principle is added.

Numeric recursion (`nat_rec`) and sequence recursion (`nat_rec_seq`) are defined from the function-type recursor `nat_rec_diagonal`; both pairs of equations are proved. `bounded_rec` is also a definition. Induction proves that the recursive `lt_flag` agrees with order, yielding base, in-range, and out-of-range equations without excluded middle. Reusing checking results for identical terms/contexts allows included examples to fit the default budget despite increased expansion. The 17 declarations comprise eight implication/quantification rules, three equality rules (natural-number substitution and U reflexivity/substitution), one induction rule, one successor/zero inequality, two recursion equations, one excluded-middle axiom, and one separation axiom. This is not claimed to be an absolutely minimal axiom system.

Besides the natural-number library's 139 `theorem` declarations, foundation files contain proofs derived from definitions.

### Natural numbers and recursive functions

1 is `succ zero`; 2 is `succ (succ zero)`. There are no opaque numeral constants or axioms identifying them with values. `one_succ` and `two_succ` are reflexivity theorems.

Addition, multiplication, and powers have the following defining recursive equations. `pred`, `factorial`, and `triangular` likewise distinguish zero and successor cases.

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

Associativity/commutativity of addition and multiplication, exponent addition, and the triangular-number formula follow by induction. [Strong induction](../examples/commons/nat/induction.ht) is also a theorem derived from ordinary Peano induction and the definition of order.

### Odd sums and squares

[The odd-sum proof](../examples/commons/nat/sums.ht) establishes `1 + 3 + … + (2n−1) = n²` by Peano induction. `sum n f` sums indices `0` through `n−1`, with summands `succ (add k k)` (`2k+1`). At `n=0`, both the empty sum and `0²` are zero. The induction step uses `square_succ`: `(n+1)² = n² + (2n+1)`, corresponding to adding an L-shaped border of the next odd number of points to a square. No new axioms are added.

### Predicate definitions

Introduction/elimination rules express the following existential/universal definitions:

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

Congruence adds multiples to both sides to avoid truncated subtraction on naturals. Divisibility/congruence transitivity and preservation under operations are proved by constructing witnesses and equations.

### Prime factors, Euclid's lemma, and infinitude

[Existence of prime factors](../examples/commons/nat/factorization.ht) takes a number greater than 1 itself if prime; otherwise strong induction descends to a proper divisor. Existence of a proper divisor follows from the prime definition and classical logic.

[The division algorithm](../examples/commons/nat/division.ht) constructs `q, r` with `n = d * q + r` and `r < d` for positive `d`, by strong induction.

[Euclid's lemma](../examples/commons/nat/euclid.ht) takes the least positive `t` satisfying `p | a * t`; division and minimality show that `t` divides `p` and `b`. Primality gives `t = 1` or `t = p`, yielding `p | a` or `p | b`.

[Infinitely many primes](../examples/commons/nat/prime_infinitude.ht) takes a prime factor of `n! + 1`. If it were at most `n`, it would divide both `n!` and `n! + 1`, hence 1, a contradiction.

### Binomial coefficients and finite sums

Binomial coefficients are defined by boundary values and Pascal's recurrence:

```text
choose n zero = 1
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n k + choose n (succ k)
```

[Coefficient identities](../examples/commons/nat/binomial_coefficients.ht) first prove `(k+1)*C(n+1,k+1)=(n+1)*C(n,k)` by induction as `choose_balance`, then express positive indices as successors. Euclid's lemma and prime divisibility yield `prime_divides_choose`.

Finite sums include prefix sums `sum`, open-interval sums `sum_between`, and diagonal sums `diagonal` over `i+j=n`. Diagonal sums satisfy:

```text
diagonal zero h = h zero zero
diagonal (succ n) h
  = diagonal n (i,j ↦ h i (succ j)) + h (succ n) zero
```

`convolution` is defined through diagonal sums:

```text
convolution n f g = diagonal n (i,j ↦ C(n,i)*f(i)*g(j))
                 = Σ(i+j=n) C(n,i)*f(i)*g(j)
```

`convolution_pascal`, `convolution_zero`, extensionality, scalar extraction, and endpoint separation are all theorems. Pascal's equation is derived from binomial recurrence and diagonal-sum properties, rather than assumed as an axiom.

[The binomial theorem](../examples/commons/nat/binomial_theorem.ht) follows by induction on `n` using these lemmas, power recurrence, and distributivity. Congruence preservation for open-interval sums also follows by induction from sum recurrence and order comparison.

### Irrationality of √2

[sqrt_two_no_positive_fraction](../examples/commons/nat/sqrt_two.ht) derives a contradiction from `b > 0` and `a * a = 2 * (b * b)` for arbitrary naturals `a, b`. It assumes neither reduction to lowest terms nor coprimality.

Euclid's lemma and the primality of 2 show that both `a` and `b` are even: `a = 2k`, `b = 2j`. Cancelling 2 gives `k * k = 2 * (j * j)` with `0 < j < b`; strong induction on the denominator yields a contradiction. `sqrt_two_irrational` rules out a rational representation using this theorem.

### Logic and classical reasoning

Logic/equality modules also derive results from basic rules. Logical quantification is over fixed `U`, arithmetic quantification over `Nat`; finite-sum proofs also quantify over natural-valued functions.

Of the De Morgan directions, `¬(A ∧ B) → ¬A ∨ ¬B` uses excluded middle; the other three directions and contraposition are constructive within intuitionistic logic. Some arithmetic theorems, including prime-factor existence, least positive witnesses, and Euclid's lemma, also use classical logic.

## Fermat's little theorem

[fermat](../examples/commons/nat/fermat.ht) follows this sequence:

1. `prime_divides_choose` makes each interior binomial term congruent to zero.
2. `sum_between_cong_zero` makes their sum congruent to zero.
3. `binomial_theorem` and proved endpoint separation yield `(x+1)^p ≡ x^p+1 (mod p)`.
4. The induction hypothesis `x^p ≡ x` gives the successor equation.
5. Natural-number induction uses prime positivity and `pow_zero_positive` for the base case.

[fermat_sum](../examples/commons/nat/fermat.ht) substitutes `x = a + b` into the proved little theorem. The usage example `fermat_application` imports and applies it.

## Verification

[rocq/example_axioms](../rocq/example_axioms/README.md) contains independent model verification of axioms. Rocq checks standard interpretations of naturals/logic and an empty-membership model satisfying the separation fragment. Excluded middle depends on Rocq's `classic`. Correspondence between `.ht` and Rocq types is manual; no general semantics-preservation proof is included.

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/commons/nat/fermat.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
# Subject modules can be checked independently
dune exec bin/main.exe -- compile examples/commons/nat/euclid.ht -o /tmp/euclid.pg
dune exec bin/main.exe -- check /tmp/euclid.pg
```

Regression tests verify that every catalog theorem registers as `Proven`. Allowed assumption vocabulary is limited to a specified list, with no new axioms in proof files. Tests recheck in declaration order preserving definition dependencies, forbid new assumptions in declarations with proofs (equivalent to `--no-axioms`), and reject incorrect conclusions and invalid proof terms.

## Russell's argument and universal sets

[The Web proof](../examples/commons/sets/russell.ht) assumes a set `u` containing every set and uses separation to form `r = {x ∈ u | x ∉ x}`. If `r ∈ r`, separation gives `r ∉ r`, so first we prove `r ∉ r`. Universality gives `r ∈ u`, and the reverse separation condition then gives `r ∈ r`, a contradiction. The final theorem `no_universal_set` expresses `¬∃u, ∀x, x ∈ u`.

Alongside existing logical/quantification rules, assumptions include [membership and separation](../examples/commons/foundation/sets.ht). Separation forms a subset of an existing set; it is not unrestricted comprehension from arbitrary properties. This demo expresses the schema using predicate parameters and assumes neither excluded middle, choice, nor the conclusion itself.

This is a separate named proof term for the same Russell argument as the [existing Rocq/ZFC verification](../rocq/zfc/README.md), written for readability on the Web. The OCaml kernel and browser checker check it, but correspondence with Rocq's first-order AST/encoding is unproved. The existing Rocq verification concerns the earlier proof terms.
