# Formal verification of proofglyph

[English](README.md) | [日本語](README.ja.md)

An independently implemented and proved Rocq type checker for proofglyph `.pg` files. The Gallina decoder and checker are extracted to OCaml and run through a dedicated CLI, without calling the existing OCaml kernel.

## Build and run

Building the extracted CLI requires ocamlfind and Zarith.

```sh
# Verify and test
make -C rocq/proofglyph
make -C rocq/proofglyph test

# Run the extracted CLI
rocq/proofglyph/_build/proofglyph check examples/identity.pg
rocq/proofglyph/_build/proofglyph check /tmp/proof.pg --prelude /tmp/prelude.pg
```

## Proved guarantees

For the cached weak-head checker (`CachedCheckerImpl.check_program`), the following are proved against declarative typing (`typing` / `valid_program`), without additional axioms or `Admitted`:

- **Soundness**: accepted declaration sequences satisfy declarative typing.
- **Completeness**: valid sequences are accepted with sufficient fuel.
- **Basic type-theoretic properties**: subject reduction, confluence, and strong normalization of typed terms.
- **Codec correctness**: decoding arbitrary bytes is equivalent to an independent lexical/stack specification.

## Sound and complete weak-head normalization

`WeakHeadSpec.v` defines weak-head normalization and recursive comparison of weak-head subterms, as used in the handwritten OCaml kernel, as inductive relations without fuel. `weak_head` does not reduce inside binders or arguments; `weak_compare` compares subterms of Π, λ, and applications. `weak_infer` also includes inference without rechecking the inferred λ type. Finite derivations represent terminated computations.

`WeakHead.v` proves the following without additional axioms:

- `whnf_steps` / `whnf_sound`: weak-head reduction is a sequence of β reductions and preserves β equivalence.
- `whnf_preserves_type`: weak-head reduction preserves typing.
- `weak_equal_sound`: successful recursive comparison implies β equivalence.
- `weak_infer_sound` / `weak_check_sound`: successful inference/proof checking satisfies declarative typing.
- `weak_check_program_sound` / `weak_accepted_program_wf`: accepted declaration sequences are valid and preserve signature well-formedness.
- `cached_infer_sound` / `inference_cache_insert_valid`: a cache keyed by the full context and term preserves soundness when it stores only successful results for the same signature.

`WeakNormalization.v` derives these results from strong normalization and confluence of typed terms:

- `strongly_normalizing_weak_head`: strongly normalizing terms reach a weak-head normal form.
- `weak_equal_complete`: recursive comparison succeeds for strongly normalizing, β-equivalent terms.
- `declarative_weak_infer`: a typable term in a well-formed signature and context has a type inferred by the weak-head system that is β-equivalent to its declarative type.

`WeakKernelImpl.v` / `WeakCheckerImpl.v` implement an executable weak-head checker with fuel. `WeakEvaluation.v` proves correspondence between weak-head reduction/comparison and the inductive specification, success with sufficient fuel, and fuel monotonicity. `WeakChecker.v` proves correspondence for executable inference, soundness, declarative completeness, and correctness of declaration-sequence/prelude checking. Completeness means success for every fuel value above some bound; it does not assert termination for arbitrary untyped terms.

The extracted CLI uses the cached weak-head checker, as does Hieratic rechecking. The full-normalization `Checker.v` remains for comparison; Hieratic output normalization still uses `normal`. `WeakExamples.v` checks that weak-head reduction leaves binders and arguments untouched, comparison examines their contents, and exhausted fuel causes rejection. `make -C rocq/proofglyph verify` runs `Print Assumptions` for the main theorems and rechecks with `rocq check`.

## Inference cache and hash-table extraction

`CacheTableImpl.v` defines a finite persistent table. `CacheTable.v` proves lookup/insert properties and invariants on stored values. `CachedCheckerImpl.v` stores successful inferred types and required fuel, keyed by the full context and term. A lookup is a hit only if the stored fuel fits the current fuel; otherwise inference is repeated. Failures are not cached, and each declaration starts with a fresh table.

`infer_correct` / `check_equivalent` / `program_equivalent` in `CachedChecker.v` prove that, with a valid cache, results agree with the uncached weak-head checker at the same fuel. The CLI starts with an empty cache, preserving the invariant. Soundness, completeness, and fuel monotonicity carry over.

`CacheExtraction.v` replaces tables and operations with OCaml `Persistent_hash`. Runtime buckets use `Hashtbl`, with collisions compared using extracted equality. Reverting differences when switching versions preserves lookup results for older tables and avoids copying the whole table in ordinary state passing. Keys are immutable, and equal keys are assumed to have equal hashes.

The Gallina table and cache are proved correct without additional axioms. Correspondence with the OCaml persistent hash table and extraction substitutions remains in the trust boundary and is checked through execution tests. `test_cache.ml` tests branched versions, long histories, collisions, Zarith keys, hits, failures, and 12,000 comparisons with uncached inference at the same fuel. General correspondence with the host OCaml hash table, shared fuel, and all handwritten code remains unproved.

## Trust boundaries and limitations

- **Axiom consistency**: consistency of registered axioms is not guaranteed.
- **Resources**: fuel measures recursion depth and does not guarantee completion within physical time or memory limits.
- **Runtime**: Rocq extraction, substitutions of arbitrary-precision integers for naturals, Zarith, the OCaml compiler/runtime, and file I/O remain trusted.

## TODO

- [ ] Prove equivalence with another LF formulation
- [ ] Prove equivalence with shift/substitution in the existing OCaml implementation
- [ ] Formally verify CLI I/O and argument handling
