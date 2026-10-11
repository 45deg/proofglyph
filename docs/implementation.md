# Implementation and verification

Structure and verification procedures for the [language specification](spec.md), covering the ordinary OCaml implementation, its Web demo, and the independent Rocq implementation. See the specification for typing rules, the [proof catalog](proofs.md) for examples, and the [Rocq README](../rocq/README.md) for formal theorems and limitations.

## Modules

| File | Responsibility |
| --- | --- |
| `lib/core/term.ml` | AST, shift, capture-avoiding substitution, type printing |
| `lib/core/kernel.ml` / `.mli` | Type inference, Π formation, β equivalence, checked signature extension |
| `lib/proofglyph/reader.ml` | Symbolic-language lexing and stack operations |
| `lib/proofglyph/writer.ml` | Encoding terms as proofglyph symbols |
| `lib/hieratic/source.ml` | Named-source parsing, imports, desugaring, name resolution, output rechecking |
| `bin/main.ml` | File I/O, CLI, error handling |
| `test/tests.ml` | Valid proofs, rejected inputs, variable-operation regression tests |
| `web/browser.ml` | Compiler/kernel JavaScript API and source-map state |
| `web/app.source.js` / `index.source.html` | Web interaction, result display, and interface |
| `web/i18n.source.js` / `translations.source.js` | Browser-language selection and English/Japanese translation dictionaries |
| `web/bundle_examples.ml` | Example bundling and proof-catalog generation |
| `web/test.cjs` | Runtime tests of JavaScript API, examples, catalog, and source maps |

Dune libraries are split into `proofglyph_core`, `proofglyph_language`, and `proofglyph_hieratic`. proofglyph depends on core; hieratic depends on proofglyph and core; neither core nor proofglyph depends on hieratic. File imports require `unix`, a hieratic dependency.

OCaml APIs are available through `Proofglyph_core.Term` / `Kernel`, `Proofglyph_language.Reader` / `Writer`, and `Proofglyph_hieratic.Source`. `Proofglyph_language.Writer.encode` writes symbols. See [Source APIs and source maps](#source-apis-and-source-maps) and the `.mli` files for API details.

The kernel signature type is abstract in `.mli`; no operation injects unchecked constants. The compiler does not manipulate kernel-internal contexts or normalizers.

Signatures and contexts are lists. Equivalence skips identical subterms and recursively compares weak-head normal forms. Inference reuses only successful results keyed by full context and term, clearing the cache on declaration registration. Cache lookups also consume fuel. This reduces repeated checking of identical expanded subterms. NbE and signature-index optimization are not implemented.

## Ordinary checking pipeline

```text
.ht → Source.load (parsing, imports)
    → Source.compile_declarations (name resolution, Writer.encode, source maps)
    → Reader.run → Kernel (recheck the entire generated .pg)
    → Source.compiled → CLI output

.pg → Reader.run (lexing, stack operations, registration) → Kernel
```

`Source.compile_declarations` resolves a declaration's type/body against preceding globals before adding its name. The parser desugars parameters into Π in types and λ in bodies. Each declaration emits its type, optional body, registration instruction, and newline. A fresh kernel rechecks the entire output; parsing/name-resolution success alone is insufficient.

The kernel weak-head normalizes application function types and uses β equivalence to compare argument/proof types. λ inference checks the domain sort and inferred body type, rejecting a body with type `Kind`. Assuming inference in well-formed contexts, it skips rechecking the resulting Π type.

`assume` / `prove` add types and origins only after successful checking; proof bodies are not retained. If Reader fails midway, earlier registrations remain in the supplied kernel. The CLI displays results and writes compilation output only after overall success.

Fuel is a shared budget consumed by inference/weak-head calls, defaulting to 1,000,000. `check --prelude` uses one kernel, so the target continues the prelude's numbering and remaining budget. Parsing, shift, substitution, and structural comparison are not fully bounded by this budget.

## Verification

```sh
dune build
dune runtest
dune exec bin/main.exe -- compile examples/basics.ht -o /tmp/basics.pg
dune exec bin/main.exe -- check /tmp/basics.pg
dune exec bin/main.exe -- compile examples/logic.ht -o /tmp/logic.pg
dune exec bin/main.exe -- check /tmp/logic.pg
dune exec bin/main.exe -- compile examples/fermat_application.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
```

Tests cover dependent context lookup, anonymous-arrow depth, substitution under binders, β-equivalent types, term generation at varying depths, mismatches, misuse of Kind, rejection of CoC-only Π formation, opacity, lack of η, malformed symbols, invalid signature references, fuel exhaustion, and assumption prohibitions.

Import tests cover relative paths, expansion at declaration positions, diamond dependencies, symlink duplicates, cycles, missing files, filename diagnostics, duplicate declarations, and forward references. Tests also check source positions, byte ranges, source-map JSON, source-declaration annotations on type errors, and preservation of existing CLI output files after loading/checking failure.

Subject libraries and the Fermat usage example compile with `Source.compile_file`; the kernel rechecks their output. Target theorems/lemmas must register as `Proven`. Arithmetic assumptions are restricted to a fixed allowlist of vocabulary, Peano axioms, logical rules, and definitions; proof files cannot introduce axioms.

Imports can interleave definitions and proofs. Tests also recompile with a signature collecting fixed assumptions first, then recheck proofs with assumption addition prohibited. Incorrect numerical equalities, range conditions, congruence moduli, square-root equations, and denominator positivity are rejected. Constructive De Morgan fragments are checked without excluded middle.

```sh
dune exec bin/main.exe -- compile examples/commons/logic/propositional.ht -o /tmp/propositional.pg
dune exec bin/main.exe -- check /tmp/propositional.pg
dune exec bin/main.exe -- compile examples/commons/equality.ht -o /tmp/equality.pg
dune exec bin/main.exe -- check /tmp/equality.pg
dune exec bin/main.exe -- compile examples/commons/nat/fermat.ht -o /tmp/fermat.pg
dune exec bin/main.exe -- check /tmp/fermat.pg
```

These are implementation/proof-term regression checks, not a formal soundness proof of the kernel itself. Recursive equations and predicate rules are explicit LF-signature definitions; naturals and arithmetic semantics are not built into the kernel. See the [proof catalog](proofs.md).

## Development

The ordinary CLI/libraries build with Dune and the OCaml standard library, including `unix` for `Unix.realpath`. The Web build requires js_of_ocaml; formal proofs require Rocq and its standard library. Merlin / OCaml LSP use Dune project settings. The ordinary parser is handwritten, without generators such as Menhir.

Expand new syntactic sugar into the named AST without changing kernel rules. Constant unfolding, η equivalence, CoC, or rewriting should be considered type-theory changes rather than mere syntax additions.

## Source APIs and source maps

`Source.parse` / `Source.compile` accept strings and reject imports with a diagnostic requesting file-loading APIs. `Source.parse_items` distinguishes imports from declarations. `Source.load path` returns expanded declarations; `Source.compile_file path` returns checked symbols, names, and declarations with file positions.

Loaded declarations can also be checked with `Source.compile_declarations`. Import state is local to each load; neither working directory nor kernel rules change.

`Source.parse_items_with` / `Source.parse_with` / `Source.load_with` take a `syntax` record describing AST construction. Existing APIs use `default_syntax`, returning the original named AST. `raw_syntax` in `rocq/hieratic/adapter.ml` preserves argument groups and sugar for differential tests between existing and extracted parsers. The Rocq CLI extracts the independent lexer/parser from `HieraticSyntaxImpl.v` and import expansion over finite file sets from `HieraticImportsImpl.v`. OCaml retains file I/O, `realpath`, and dependency-table collection. Equivalence to independent parsing/import specifications and sufficient internal fuel are proved, and computation examples and comparisons are tested.

Source maps relate original declarations to generated bytes. `Source.compiled.sourcemap` stores constant numbers, names, source positions, and output byte ranges per declaration; `Source.sourcemap_json result` serializes them. Ranges are recorded during encoding; results are returned only after successful rechecking.

`Source.annotate_assembly_error` appends original position/name to diagnostics within a declaration's byte range. Diagnostics outside ranges remain unchanged; compilation type errors also use it.

`Source.compile_file` maps use canonical absolute paths; `Source.compile` uses `file = null`. Declarations from `Source.parse_items ~file` retain that supplied path. After checking, the CLI writes the map, then symbols. It compares existing destinations by device/inode, or by canonical parent directory and filename, rejecting identical destinations. Atomic updates across both files are not guaranteed on I/O errors.

## Web demo

`web/browser.ml` exposes the compiler/kernel through js_of_ocaml as `globalThis.proofglyph`, including `examples`, `compileAt`, `compileProject`, `projectFiles`, `checkMapped`, and `check`. Functions return `{ok, output}`; successful compilation also returns source-map JSON. Every run uses a fresh kernel with default fuel. Browser imports resolve within bundled/editable project files.

`compileAt` attaches display paths and discards prior results when invoked. `checkMapped` uses the latest successful compilation map only for exactly matching output; otherwise it falls back to `cN`. `check` never uses a map.

`web/bundle_examples.ml` bundles original example sources with their import statements. The browser resolves dependencies at compilation time, including edits made in file tabs, and loads each dependency once.

`web/dune` generates `examples_data.ml` from `examples/` and copies the interface, scripts, and catalog to distribution files. `--catalog` cross-references the table between `<!-- proof-catalog:start -->` and `<!-- proof-catalog:end -->` in `docs/proofs.md` with source declarations, generating names, paths, and line numbers. Heading text does not affect generation. Subject/proposition text becomes display keys, so editing it changes keys. The catalog is not updated automatically; regenerate it when examples or the table change.

`web/app.source.js` fetches the catalog and creates grouped choices. Editing source or proofglyph invalidates maps/results. Successful compilation triggers checking; all returned declaration results produce success cards. Input compilation/checking runs entirely in the browser.

`web/i18n.source.js` selects the first supported `en` or `ja` language from `navigator.languages`, then `navigator.language`, falling back to English. It updates `html.lang`, text, and accessible labels using `translations.source.js`, and handles `languagechange`. Static text translations preserve the existing DOM structure and inline markup. Dynamic messages use named keys and parameter interpolation. Catalog keys stay English, with Japanese display labels in the dictionary. The compiler's diagnostics and user/example source text are preserved. No external i18n dependency is required.

```sh
dune exec web/bundle_examples.exe -- --catalog examples > /tmp/proofglyph-catalog.json
cp /tmp/proofglyph-catalog.json examples/catalog.json
dune build @web/browser
node web/test.cjs
node web/worker.test.cjs
node web/i18n.test.cjs
```

`web/test.cjs` checks all bundled examples, invalid imports, catalog/document/declaration positions, named display, errors, and stale-map fallback. `web/i18n.test.cjs` checks language negotiation, dictionaries, and DOM translation. These Node.js tests do not verify visual layout or browser interaction.

## Rocq implementation and formal proofs

| Directory | Implementation / proofs |
| --- | --- |
| `rocq/proofglyph/` | AST, declarative typing, substitution, subject reduction, confluence, strong normalization, sound/complete `CachedCheckerImpl.v`, persistent-table hash extraction, OCaml extraction, handwritten CLI |
| `rocq/hieratic/` | Sugar AST/expansion, name resolution/translation, shared proofglyph codec, independent lexer/parser/import expansion, extracted code, I/O adapter |
| `rocq/calculi/` | Independent NK/LK, correspondence with a fixed LF signature, LK cut elimination, direct AST output and rechecking |
| `rocq/zfc/` | First-order/ZFC proof systems, formula encoding, translation/reconstruction with fixed signatures, generated proofs and Russell rechecking |

`proofglyph` extracts the weak-head checker proved equivalent to the uncached version, sound, and complete in `CachedChecker.v`; it never calls the ordinary OCaml kernel. Its shared extracted codec constructs declarations. Arbitrary-byte decoding is proved equivalent to an independent lexical/stack specification. I/O, CLI handling, and index-limit prechecks are unverified.

The hieratic runtime path is:

```text
.ht → adapter.ml (I/O, realpath, dependency collection)
    → prepare_files / parse_hieratic / load_hieratic (extracted parser, path mapping, imports)
    → desugar_program → lower → check_program → encode_proofglyph

.pg → decode_proofglyph → check_program
```

The CLI does not call the ordinary lexer/parser, import loader, name resolver, or kernel. Ordinary AST conversions and `raw_syntax` remaining in `adapter.ml` serve differential testing. Proofs cover correspondence to independent lexical/grammar/import specifications, sufficient internal fuel, and the path from stored bytes through output/rechecking. The path is split into `FileSpec` / `FileImpl` / `FileCompile`; language theory does not depend on implementation, nor implementation on correspondence proofs. `rocq/test_layers.py` checks these boundaries.

Rocq fuel measures recursion depth. Both CLIs default to 2048, allowing 1–100000. proofglyph also limits input indices to 100000. The hieratic codec uses Rocq naturals; extraction does not replace them with machine integers. Completeness with sufficient fuel does not guarantee success within CLI limits or physical resources.

```sh
make -C rocq verify
make -C rocq test
```

The root Makefile verifies proofglyph, hieratic, calculi, and zfc in that order. Run individual projects with commands such as `make -C rocq/proofglyph test`. `ROCQ` / `OCAMLC` select executables. Generated proof data, Rocq output, extracted code, and CLIs live in each directory's `_build/`.

`verify` compiles proofs, runs `Print Assumptions` on main theorems, and rechecks with `rocq check`. `test` additionally runs extracted CLIs/generated proofglyph and compares with the ordinary implementation. Formal proofs and differential tests have different guarantees; tests alone do not prove the ordinary implementation correct.

NK/LK and ZFC equivalence theorems concern ASTs over their specified fixed signatures. They do not guarantee general correspondence to generated bytes, correctness of the ordinary OCaml implementation, or axiom consistency. Rocq's kernel/extraction, OCaml compiler/runtime, and I/O remain trusted. See the [Rocq README](../rocq/README.md).

## Transparent definition expansion

The ordinary Hieratic compiler expands closed `def` bodies at subsequent references and β-reduces output. It also checks pre-reduction terms, rejecting invalid erased arguments. An independent reader/kernel rechecks `.pg`. `theorem` retains opaque references. Both `symbol` and `axiom` register assumptions with `:`, while the library distinguishes vocabulary from unproved principles.

Browser API `type` is the expanded checked type; `surfaceType` is the corresponding original named type, preferred for display. Directly edited `.pg` has no `surfaceType`. Rocq also uses extracted parsers, expanders, β reducers, and checkers. `Elaboration.v` formalizes transparent expansion and proves compilation soundness/completeness including checking before/after reduction. Original named-type display and the browser UI are outside the proof scope.
