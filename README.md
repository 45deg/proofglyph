# proofglyph

[English](README.md) | [日本語](README.ja.md)

A small proof checker written in OCaml, based on dependent type theory (the λΠ calculus / LF). It checks proofs written in the symbolic proofglyph language. The companion hieratic language compiles named syntax into proofglyph.

Hieratic input:

```text
symbol A : Type;
def id (x : A) : A := x;
```

Generated proofglyph code (proofglyph has no comment syntax):

```text
*:#0#0>#0$0\!
```

The kernel handles only de Bruijn indices, `Type/Kind`, Π, λ, application, and opaque constants. Type comparison uses β equivalence; registered constant bodies are never unfolded. Hieratic expands `def` bodies at subsequent references. The compiler performs expansion and β reduction, and the kernel rechecks the generated terms. A `theorem` is an opaque proof that is not expanded. `symbol` declares undefined types and symbols; `axiom` declares trusted logical rules and mathematical axioms. Both count as assumptions in the kernel.

## Build and run

Requires OCaml and Dune 3.0 or later, with no external library dependencies.

```sh
dune build bin/main.exe
dune runtest
```

### CLI usage

```sh
# Compile hieratic into proofglyph
dune exec bin/main.exe -- compile examples/basics.ht -o /tmp/basics.pg

# Check proofglyph
dune exec bin/main.exe -- check /tmp/basics.pg

# List each constant's type and origin (assumption or proven)
dune exec bin/main.exe -- inspect /tmp/basics.pg
```

- `-o FILE` (`compile`): output file; defaults to standard output. Written only after successful checking.
- `--sourcemap FILE` (`compile`): write a declaration-level source map as JSON.
- `--prelude FILE` (`check`): load assumptions from a separate file and prohibit new assumptions (`:`) in the target file.
- `--no-axioms` (`check`): prohibit assumptions (`:`) in the file.
- `--fuel N` (all commands): shared budget consumed by type inference and weak-head normalization (default: 1,000,000). This is not a time or memory limit.

Split hieratic sources with `import "relative/path.ht";`. Compiling the root file expands its dependencies into a single `.pg` file.

## Web demo

The compiler and kernel are compiled to JavaScript, so compilation and checking run entirely in the browser.

```sh
python3 web/dev.py
```

Open [http://127.0.0.1:8765](http://127.0.0.1:8765).

The interface and documentation support English and Japanese. The first supported language in `navigator.languages` (falling back to `navigator.language`) selects the language; other languages fall back to English. Browser language changes are applied without reloading.

Compilation and type checking run in a Web Worker. You can edit while processing; the cancel button or an input change stops the running operation. Workers keep the interface responsive but do not reduce the computational cost of proofs.

```sh
dune build @web/browser
node web/test.cjs
node web/worker.test.cjs
node web/i18n.test.cjs
```

## Formal proofs and trust boundaries (Rocq)

Kernel type checking does not establish the consistency of the supplied axioms. The trusted arithmetic assumptions include logic, equality, Peano axioms, and axioms for primitive recursion at function types. Definitions and introduction/elimination rules for individual operations and predicates are expressed as `def` and proved `theorem` declarations.

[rocq/](rocq/README.md) contains an independent Rocq implementation and formal proofs. The guarantees below apply to the Rocq implementation; they do not formally prove the correctness of the ordinary OCaml implementation. Rocq is not required for ordinary use.

| Component | Guarantee |
| --- | --- |
| [proofglyph](rocq/proofglyph/README.md) | Checker soundness with respect to declarative typing, and completeness with sufficient fuel. Extracted OCaml code can independently recheck `.pg` files. |
| [hieratic](rocq/hieratic/README.md) | Equivalence to parsing/import specifications; soundness and completeness of name resolution, definition expansion, and checking before and after reduction; round trips for `.pg` encoding/decoding. |
| [Propositional NK/LK](rocq/calculi/README.md) | Correspondence between proof terms over a fixed LF signature and NK/LK derivations, plus LK cut elimination. |
| [ZFC](rocq/zfc/README.md) | For closed formulas, equivalence between ZFC provability and the existence of a typed proof term over a fixed LF signature. |

The NK/LK and ZFC theorems concern ASTs inside Rocq. The general correspondence between generated proofglyph bytes and those ASTs is not proved. See each README for the detailed guarantees and trust boundaries.

```sh
make -C rocq verify
make -C rocq test
```

## Documentation and examples

- [Specification](docs/spec.md): type theory, proofglyph/hieratic grammars, typing, and equivalence.
- [Implementation](docs/implementation.md): modules, checking pipelines, and source maps.
- [Proof catalog](docs/proofs.md): included proofs in logic, equality, natural numbers, and number theory.
- [Arithmetic library](examples/commons/README.md): operations on natural numbers, divisibility, the binomial theorem, infinitely many primes, irrationality of $\sqrt{2}$, and more, based on Peano and recursion axioms.
- [Basics](examples/basics.ht) / [Logic](examples/logic.ht) / [Applying Fermat's little theorem](examples/fermat_application.ht)
