# Formal proofs in Rocq

[English](README.md) | [日本語](README.ja.md)

Formal proofs, extracted code, and tests related to proofglyph, written in Rocq (formerly Coq). Rocq is not required for the ordinary OCaml build.

| Subproject | Namespace | Scope |
| --- | --- | --- |
| [proofglyph/](proofglyph/README.md) | `Proofglyph.Language` | Core language typing; checker soundness and completeness |
| [hieratic/](hieratic/README.md) | `Proofglyph.Hieratic` | Verified parsing, imports, transparent definition expansion, and type checking |
| [calculi/](calculi/README.md) | `Proofglyph.Calculi` | Propositional NK/LK, correspondence with LF, and cut elimination |
| [example_axioms/](example_axioms/README.md) | `Proofglyph.ExampleAxioms` | Independent model verification of the 17 example axioms |
| [zfc/](zfc/README.md) | `Proofglyph.Zfc` | Equivalence between the ZFC proof system and its proofglyph encoding |

## Verify and run

Requires Rocq, OCaml, Dune, Make, Python 3, and ocamlfind and Zarith for the extracted CLIs.

```sh
# Verify and test all subprojects
make -C rocq verify
make -C rocq test

# Run the extracted CLIs
rocq/proofglyph/_build/proofglyph check examples/identity.pg
rocq/hieratic/_build/hieratic check examples/basics.ht
```

For individual subprojects, use commands such as `make -C rocq/proofglyph test`.

Each `_CoqProject` controls compilation order for proofglyph/hieratic. Make copies proofs into `_build/`, keeping generated files, including extracted code, there. Verification stamps trigger revalidation when proof sources, build settings, or the dependent proofglyph verification results change.

Dune builds the ordinary OCaml implementation and proof-input generators. Make and `ocamlc` handle Rocq verification and compilation of the extracted CLIs. These CLIs are built separately from the ordinary Dune build.

## Design

proofglyph and hieratic separate **language specifications, implementations, and correspondence proofs**:

- **Specifications**: syntax, typing rules, and evaluation, defined declaratively without depending on algorithms.
- **Implementations**: checkers, translators, parsers, and codecs.
- **Correspondence proofs**: agreement with specifications, soundness, and completeness.

Proofs use `nat`. Extraction to OCaml replaces it with Zarith arbitrary-precision integers through the standard `ExtrOcamlNatBigInt`. This avoids allocating unary naturals and overflowing machine integers, but the extraction substitutions and Zarith enter the trust boundary. CLI input limits remain to control resource usage. Changing the representation alone does not improve the complexity of recursion that decrements a natural number.
