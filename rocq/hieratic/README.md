# Formal verification of hieratic

[English](README.md) | [日本語](README.ja.md)

A compiler implemented and proved in Rocq, covering parsing, translation, and output from high-level `.ht` to low-level `.pg`. The parser and translator are extracted to OCaml and connected to the shared proofglyph codec and type checker.

## Build and run

Building the extracted CLI requires ocamlfind and Zarith.

```sh
# Verify and test
make -C rocq/hieratic
make -C rocq/hieratic test

# Run the extracted CLI
rocq/hieratic/_build/hieratic check examples/basics.ht
rocq/hieratic/_build/hieratic compile examples/basics.ht -o /tmp/basics.pg
rocq/hieratic/_build/hieratic check-proofglyph /tmp/basics.pg
```

## Proved guarantees

The complete path from high-level syntax through name resolution to `.pg` output and rechecking has the following proofs, without additional axioms or `Admitted`:

- **Parsing and import correctness**: byte-level lexing/parsing and import expansion are equivalent to independent specifications.
- **Sound and complete name resolution and translation**: translation from named syntax to de Bruijn indices is unique and preserves declaration order, kinds, and scope.
- **.pg round trips and rechecking**: translated declaration sequences round-trip through byte encoding/decoding, and generated `.pg` files can be independently rechecked.

## New Hieratic extensions

`symbol` is parsed as an assumption, like `axiom`. `def` bodies are expanded at later references; `theorem` remains opaque. Expander correctness and compilation soundness/completeness are proved against the independent expansion and evaluation relations in `Elaboration.v`. Both expanded terms before reduction and reduced terms are checked, rejecting invalid arguments that reduction would erase. Closed definition expansion is also proved not to capture local variables.

The extracted CLI uses this path by default. `--elaborate` is a compatibility alias; processing is not delegated to the host OCaml compiler. Agreement with the existing OCaml output is tested on individual examples, separately from a general equivalence proof between implementations.

## Trust boundaries and limitations

- **Extraction and integers**: naturals are extracted to Zarith arbitrary-precision integers via `ExtrOcamlNatBigInt`. These substitutions and Zarith remain trusted.
- **Host environment**: OCaml handles file I/O, canonical paths (`realpath`), and dependency collection.
- **Independent named-language theory**: the named language's type theory is not independently formalized; verification uses a declarative translation relation to the proofglyph core.
- **Differences from the ordinary OCaml kernel**: recursive weak-head comparison and skipping identical terms are proved sound and complete. An inference cache keyed by context and term is proved to agree with the uncached checker at the same fuel. Extraction replaces the table with a persistent hash table; correspondence with that runtime is tested. Fuel measures recursion depth rather than the host's shared budget, so consumption and runtime differ.
- **Resources**: recursion-depth fuel does not guarantee completion within physical time or memory limits.

## TODO

- [ ] Independently formalize typing, substitution, and α equivalence for the named language
- [ ] Prove exact byte-level equivalence with the existing OCaml reader/writer
- [ ] Preserve CLI line/column positions and improve diagnostics
