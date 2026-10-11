# ZFC over proofglyph

[English](README.md) | [日本語](README.ja.md)

A Rocq definition of first-order ZFC axioms and natural deduction, with a formal proof that **for closed formulas, ZFC provability is equivalent to the existence of a typed proof term over a fixed LF signature**.

## Build and run

```sh
# Verify and test
make -C rocq/zfc test

# Check Russell's example (no universal set)
rocq/proofglyph/_build/proofglyph check rocq/zfc/_build/russell/proofs.pg --prelude rocq/zfc/_build/russell/prelude.pg
```

## Proved guarantees

- **Equivalence (`ZFC_proofglyph_iff`)**: for every closed formula $\phi$, ZFC provability is equivalent to the existence of a typed proofglyph term over the fixed LF signature defined in Rocq, without additional axioms or `Admitted`.
- **Concrete example**: a derivation of the nonexistence of a universal set ($\neg \exists U, \forall x, x \in U$), using Russell's paradox, is generated as a proofglyph term and checked for acceptance.

## Reducing the axioms

The empty-set axiom has been removed from the full `zfc_axiom` and `proof_prelude.ht`. Fixed axioms were reduced from eight to seven; separation and replacement schemas remain.

`empty_set_derived` in `Empty.v` derives an empty set from the infinity axiom's condition that its set contains an empty set, at any variable depth and under any assumptions. This derivation can replace uses of the old empty-set axiom. `empty_set_not_primitive` verifies that the empty set is not a primitive axiom.

`empty_export.py` inserts the derivation's proof term at a marker in `proof_certificates.ht`, generating `_build/deep/source.ht`. Rocq and both checkers verify the output. The earlier small illustrative `prelude.ht` retains `empty_exists` because it has no infinity axiom.

## Trust boundaries and limitations

- **Axiom consistency**: this does not prove consistency of ZFC or the existence of a model.
- **Byte correspondence**: correspondence between generated proofglyph bytes and Rocq ASTs is not formally verified; tests compare them.

## TODO

- [x] Derive the empty-set axiom from infinity within the system and remove it from the full primitive rules
- [ ] Formally verify correspondence between output bytes and Rocq ASTs
- [ ] Prove equivalence with the choice-function form of the axiom of choice
