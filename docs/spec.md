# proofglyph language specification

## 1. Scope and term structure

This specifies a λΠ calculus (LF-style dependent type theory) with β equivalence only. Types and proof terms share the same syntax. CoC, η equivalence, constant unfolding, recursive definitions, built-in inductive types, user-defined rewriting, implicit arguments, holes (metavariables), unification, and tactics are unsupported.

The languages are called proofglyph and hieratic; the type-checking core is the kernel. “Checking” means executing type checking, while “formal verification” means proving specifications or theorems in a proof assistant. Registered constants distinguish between origins `Assumption` and `Proven`.

Types/terms have seven AST forms:

```text
t ::= Type | Kind | Var(n) | Const(n)
    | Pi(t,t) | Lam(t,t) | App(t,t)
```

`n` is nonnegative. Constants are numbered from zero in registration order. Only the second argument (body) of Π and λ binds a new variable. `Var(0)` is the innermost bound variable, using de Bruijn indices. Type annotations follow the same binding rules.

## 2. proofglyph (.pg)

```ebnf
program = { token } ;
token = "*" | "^" | "$", natural | "#", natural
      | ">" | "\\" | "@" | ":" | "!" ;
natural = digit, { digit } ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
```

Spaces, tabs, CR, and LF are ignored between tokens, but cannot separate `$` / `#` from their digits. Numbers use longest-match scanning; leading zeros are allowed. Indices outside OCaml's `int` range are rejected. There are no comments, instruction aliases, or arbitrary-character skipping.

The rightmost stack element is the top (most recently pushed term).

| Instruction | Operation |
| --- | --- |
| `*` | `S → S Type` |
| `^` | `S → S Kind` |
| `$n` | `S → S Var(n)` |
| `#n` | `S → S Const(n)` |
| `>` | `S A B → S Pi(A,B)` |
| `\` | `S A b → S Lam(A,b)` |
| `@` | `S f x → S App(f,x)` |
| `:` | Register an assumption when the stack is exactly `[A]`, then empty it |
| `!` | Check and register `t:A` when the stack is exactly `[A,t]`, then empty it |

Construction does not type-check. Registration checks closed terms. Unknown constants, free variables, stack underflow, extra terms at registration, a nonempty stack at EOF, and invalid characters are errors.

```text
*:#0#0>#0$0\!
```

This registers the assumption `c0 : Type`, checks `λ x:c0. x`, and registers `c1 : Π x:c0. c0`.

`^` can construct `Kind`, but `^:` is rejected because `Kind` itself has no type.

## 3. Typing and equivalence

A sequence of registered constant types is a signature. `Kind` represents kinds; `Type` and `Kind` are collectively called sorts.

The judgment is `Σ; Γ ⊢ t : A` under signature Σ and context Γ.

- `Type : Kind`; `Kind` has no type.
- Variable lookup shifts the stored type to the current depth.
- Constants have the closed types stored in Σ.
- If `A : Type` and `Γ,x:A ⊢ B:s`, where `s ∈ {Type,Kind}`, then `Π x:A.B : s`.
- If `A : Type`, `Γ,x:A ⊢ b:B`, and `Π x:A.B` can be formed, then `λ x:A.b : Π x:A.B`.
- If `f : Π x:A.B` and `u:A`, then `f u : B[u/x]`.
- Type comparison admits β equivalence; testing this relation is the equivalence check.

Thus the only Π-formation sort pairs are `(Type,Type)` and `(Type,Kind)`. `Π A:Type.A→A` is rejected.

Context types are stored relative to the context immediately before introducing the variable. Lookup at index `n` applies `shift(n+1,0,type)`.

β reduction is `(λ x:A.b) u → b[u/x]`. Substitution avoids capture and adjusts indices for the removed binder. Application inference uses weak-head normalization. Equivalence accepts structurally identical subterms directly and recursively compares weak-head normal forms of differing parts. The de Bruijn representation incorporates α equivalence. η equivalence, proof irrelevance, and constant unfolding are unsupported.

## 4. Registering opaque constants

Opaque constants store only a type and origin; definition/proof bodies are not unfolded.

- `assume A` checks in the empty context that `A` has sort `Type` or `Kind`, then registers a new assumption constant.
- `prove A t` checks well-formedness of `A` and `t:A`, then registers a new proven constant. Failed declarations are not registered.

Neither form may refer to itself or later constants.

Registered constants retain their type and origin (`Assumption` / `Proven`). The proof term `t` is not retained in the kernel signature; the constant is opaque after registration.

Logic, equality, Peano, and recursion principles are signature assumptions (`Assumption`). `def` declarations for predicates/operations and `theorem` declarations proving their rules/equations are registered as checked (`Proven`).

## 5. hieratic (.ht)

```ebnf
program = { import | declaration } ;
import = "import", path, ";" ;
path = '"', path_character, { path_character }, '"' ;
declaration
  = ("axiom" | "symbol"), name, { parameter }, ":", term, ";"
  | ("def" | "theorem"), name, { parameter },
    ":", term, ":=", term, ";" ;
parameter = "(", name, { name }, ":", term, ")" ;
term
  = "forall", parameter, { parameter }, ",", term
  | "fun", parameter, { parameter }, "=>", term
  | arrow ;
arrow = application, [ "->", term ] ;
application = atom, { atom } ;
atom = name | "Type" | "Kind" | "(", term, ")" ;
```

`symbol` declares undefined types/symbols. `axiom` declares trusted logical rules and mathematical axioms without proofs. Both register kernel assumptions and are prohibited by `--no-axioms`. `def` and `theorem` type-check their bodies. Later references to `def` expand its body at compile time; `theorem` references remain opaque constants.

Identifiers are ASCII `[A-Za-z_][A-Za-z0-9_']*`. `symbol axiom def theorem import forall fun Type Kind` are reserved. `//` starts a comment until the end of the line. There are no numeric literals or infix arithmetic operators.

`import "../examples/commons/nat/addition.ht";` loads declarations at that position. Relative paths resolve against the canonical importing file's directory; absolute paths are allowed. Paths are nonempty, double-quoted strings without quotes, newlines, or backslashes. There is no escape syntax.

Loading is depth-first in declaration order. `realpath` identifies canonical files, each loaded once per compilation; aliases using `./`, `../`, or symbolic links refer to the same file. Cycles and missing files are errors.

There are no namespaces, aliases, or selective imports. Imported declarations share the global signature; duplicate names across files are rejected. Declarations appearing after an import cannot be forward-referenced.

Application associates left; arrows associate right. Application binds more tightly than arrows. Parenthesize `forall` or `fun` when used as application arguments.

Name resolution searches innermost locals first, then preceding globals. Local shadowing is allowed. Duplicate globals, forward references, and self-reference are rejected. `_` is an ordinary name, not a hole.

`(x y : A)` expands into sequential binders `(x : A) (y : A)`, including when shadowing occurs.

| Syntax | Expansion |
| --- | --- |
| `f x y` | `App(App(f,x),y)` |
| `A -> B` | `Pi(A,B)` with an unnamed binder |
| `forall (x:A), B` | `Pi(A,B)` |
| `fun (x:A) => b` | `Lam(A,b)` |
| Declaration parameters | Add outer Π binders to the type and λ binders to the body |
| `symbol/axiom name : A;` | `encode(A)` followed by `:` |
| `def/theorem name : A := t;` | `encode(A) encode(t) !` |

Anonymous arrow binders also count toward de Bruijn depth. Types and bodies resolve names according to their respective binding structures.

After `def id (x:A) : A := x;`, expansion and β reduction make `id a` equal to `a`. Hieratic expands closed bodies when generating `.pg`; it does not add unfolding to the kernel. Self/forward references are forbidden, and expansion's β-reduction count has the same limit as `fuel`. Both pre-reduction terms and generated reduced `.pg` are checked, so invalid arguments erased by reduction are rejected.

Original named types are retained for display, while checking uses expanded types. Direct `.pg` checking does not use the original named types. The Rocq CLI also uses extracted implementations from parsing through expansion, β reduction, and checking before/after reduction. Their soundness and completeness are proved against declarative translation, evaluation, and typing relations. `--elaborate` is a compatibility alias.
