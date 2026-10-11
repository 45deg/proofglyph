# Proof library

[English](README.md) | [日本語](README.ja.md)

Related theorems are grouped into `.ht` modules by subject. Import the module you need directly; its definitions and preceding proofs are loaded automatically. There is no compatibility entry point that loads every subject at once.

Using addition theorems from a file in `examples/`:

```text
import "commons/nat/addition.ht";

theorem commute_example (a b : Nat) : Prf (Eq (add a b) (add b a))
  := add_comm a b;
```

Every module can be compiled and checked directly.

```sh
dune exec bin/main.exe -- compile examples/commons/nat/addition.ht -o /tmp/addition.pg
dune exec bin/main.exe -- check /tmp/addition.pg
```

## Structure

| Location | Contents |
| --- | --- |
| [foundation/](foundation/) | Trusted vocabulary, logical rules, Peano axioms, equality rules, predicate and recursive-function definitions, and set separation. 17 modules by subject. |
| [logic/propositional.ht](logic/propositional.ht) | Implication composition, argument exchange/duplication, conjunction/disjunction, contraposition, constructive De Morgan laws. |
| [logic/classical.ht](logic/classical.ht) | Directions of De Morgan laws requiring excluded middle. |
| [logic/quantifiers.ht](logic/quantifiers.ht) | Universal/existential quantification over `U`, function composition. |
| [equality.ht](equality.ht) | Symmetry, transitivity, and congruence of equality over `U`. |
| [nat/](nat/) | Equality, arithmetic, order, and number theory over natural numbers. 25 modules, 139 theorems. |
| [sets/russell.ht](sets/russell.ht) | No universal set, derived from separation without excluded middle or choice. |

In `foundation/`, undefined types and logical symbols use `symbol`; trusted logical, equality, Peano, recursion, and separation principles use `axiom`; operations and predicates use `def`; derived rules and equations use `theorem`. Introduction/elimination rules for `And`, `Or`, `Not`, `False`, `Exists`, `Divides`, `Prime`, order, parity, congruence, and others are proved, as are equations for addition, multiplication, powers, sums, and binomial coefficients. Recursion axioms are explicit in `recursion.ht`; they are not claimed to follow from Peano axioms alone. Sequence recursion and bounded recursion are definitions with proved equations. `symbol` also counts as an assumption in the kernel. See the [proof catalog](../../docs/proofs.md) for details and the list of proofs.

`import` loads each canonical file once. Namespaces are shared, so the equality/quantifier signature over `U` and the same-named natural-number signature must be used separately. For equality on naturals, use `nat/basic.ht`.

## Natural-number and number-theory modules

| Module | Contents |
| --- | --- |
| [basic.ht](nat/basic.ht) | Equality, case analysis, reflexivity of 1 and 2. |
| [addition.ht](nat/addition.ht) | Identity, successor, associativity, commutativity, cancellation. |
| [multiplication.ht](nat/multiplication.ht) | Identity, distributivity, associativity, commutativity. |
| [order.ht](nat/order.ht) | Comparison, positivity, and contradictions from order defined through addition. |
| [ordered_multiplication.ht](nat/ordered_multiplication.ht) | Cancellation by a positive factor and positivity of products. |
| [powers.ht](nat/powers.ht) | Addition of exponents, powers of 1, powers of 0 with positive exponents. |
| [parity.ht](nat/parity.ht) | Sums of two even or two odd numbers. |
| [sums.ht](nat/sums.ht) | Finite-sum equations, index shifts, triangular-number formula, odd sums and squares. |
| [divisibility.ht](nat/divisibility.ht) | Transitivity, preservation under sums/products, cancellation from addition. |
| [congruence.ht](nat/congruence.ht) | Equality laws; preservation under addition, multiplication, and powers. |
| [classical.ht](nat/classical.ht) | Double-negation elimination from excluded middle. |
| [induction.ht](nat/induction.ht) | Strong induction from Peano induction. |
| [division.ht](nat/division.ht) | Least positive witness, division algorithm, divisibility of a least multiple. |
| [primes.ht](nat/primes.ht) | Prime positivity/divisors, primality of 2, coprimality lemmas. |
| [factorization.ht](nat/factorization.ht) | Proper divisors and existence of prime factors. |
| [euclid.ht](nat/euclid.ht) | Euclid's lemma and divisibility of squares. |
| [prime_infinitude.ht](nat/prime_infinitude.ht) | Factorial lemmas and infinitely many primes. |
| [binomial_coefficients.ht](nat/binomial_coefficients.ht) | Range, diagonal, endpoints, Pascal's relation, coefficient identities. |
| [diagonal.ht](nat/diagonal.ht) | Diagonal finite-sum equations, additivity, index shifts. |
| [convolution.ht](nat/convolution.ht) | Recurrence for binomial-weighted finite sums; equality, scalar, and identity lemmas. |
| [binomial_theorem.ht](nat/binomial_theorem.ht) | Binomial theorem and its specialization with one variable equal to 1. |
| [prime_binomial.ht](nat/prime_binomial.ht) | Prime divisibility of interior binomial coefficients. |
| [modular_sums.ht](nat/modular_sums.ht) | Congruence preservation for open-interval finite sums. |
| [fermat.ht](nat/fermat.ht) | Binomial-expansion congruence lemma, Fermat's little theorem, application to sums. |
| [sqrt_two.ht](nat/sqrt_two.ht) | Parity of squares, coprime contradiction, irrationality of √2 by infinite descent. |

The basic dependency chain is `basic → addition → multiplication`, followed by order, divisibility, and other subjects. Each file lists its exact dependencies at the beginning. See [logic composition](../logic.ht) and [applying Fermat](../fermat_application.ht) for usage examples.
