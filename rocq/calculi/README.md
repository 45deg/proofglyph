# Propositional NK / LK over proofglyph

[English](README.md) | [日本語](README.ja.md)

Classical propositional natural deduction (NK) and sequent calculus (LK), encoded as LF proof terms with a fixed proofglyph prelude. Rocq proofs establish correspondence between NK/LK derivations and proofglyph terms, and the LK cut-elimination theorem.

## Build and run

```sh
# Verify and test
make -C rocq/calculi test

# Generate and check proofglyph files
make -C rocq/calculi export
dune exec bin/main.exe -- check rocq/calculi/_build/proofs.pg --prelude rocq/calculi/_build/prelude.pg
```

`export` also generates named `prelude.ht` / `proofs.ht`, and separate NK and LK versions: `nk-prelude.ht` / `nk-proofs.ht` and `lk-prelude.ht` / `lk-proofs.ht`. Types, logical symbols, and judgments use `symbol`; inference rules use `axiom`; proved examples use `theorem`. The shared prelude has 18 `symbol` and 38 `axiom` declarations. Both assumption forms become `Assume` in the kernel, so the existing `.pg` contents are unchanged. Tests also compare compiled `.ht` output with directly generated `.pg` files.

## Proved guarantees

- **Adequacy**: over the fixed LF signature, every NK/LK derivation has a corresponding LF proof term, and a derivation can be recovered from every closed LF proof term.
- **Cut elimination**: every LK derivation using cut has a derivation without cut.

## Trust boundaries and limitations

- **Scope**: atomic propositions, ⊥, ⊤, implication, conjunction, disjunction, and negation. Quantifiers and equality are excluded.
- **Existence proofs**: derivation and cut-elimination results prove existence; they are not executable rewriting algorithms.
- **Byte correspondence**: correspondence between generated proofglyph bytes and Rocq ASTs is unproved; tests compare them.

## TODO

- [ ] Extend to first-order predicate logic (quantifiers and equality)
- [ ] Implement and verify an executable cut-elimination transformer
- [ ] Direct translations between NK and LK
