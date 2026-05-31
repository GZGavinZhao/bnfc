# Lean 4 Backend — Implementation Notes

This document captures the design decisions, trade-offs, and known
limitations of the BNFC Lean 4 backend, primarily for future
maintainers (human or AI) who want to extend it.

The backend was added in mid-2026 as the first release of Lean
support; treat everything below as "version 1" and revise freely.

## 1. What's generated

For an LBNF grammar `LANG.cf`, `bnfc --lean LANG.cf` writes a
self-contained Lake project to the output directory:

| File                  | Role                                                 |
| --------------------- | ---------------------------------------------------- |
| `AbsLANG.lean`        | AST: one `inductive` per category, in a `mutual`     |
| `LexLANG.lean`        | Hand-rolled longest-match lexer (no external deps)   |
| `ParLANG.lean`        | Recursive-descent parser with precedence climbing    |
| `PrintLANG.lean`      | Pretty-printer (`AST → String`)                      |
| `TestLANG.lean`       | CLI driver (reads file or stdin, lex + parse + dump) |
| `ParserRuntime.lean`  | Tiny zero-dep combinator library (~150 LOC)          |
| `lakefile.toml`       | Lake build manifest                                  |
| `lean-toolchain`      | Pinned Lean version (`leanprover/lean4:v4.30.0`)     |

The user runs `lake build` and gets an executable
`.lake/build/bin/testLANG` that they can pipe input into.

## 2. Why the backend looks the way it does

### 2.1 Why we *don't* delegate to Haskell via FFI (the Agda strategy)

The Agda backend works by emitting an Agda module that uses
`{-# COMPILE GHC ... #-}` pragmas to call Haskell parsers generated
by Happy/Alex. Lean 4 has no equivalent of the Agda-Haskell FFI:
`@[extern]` calls into C, not Haskell. There is no clean way to wire
Happy/Alex output into a Lean program. So the Agda blueprint is the
wrong template — Lean has to generate its own complete parser.

### 2.2 Why we *don't* depend on `Std.Internal.Parsec`

`Std.Internal.Parsec` ships with the Lean 4 stdlib and provides a
proper Parsec-style monad with `Monad`, `Alternative`, `attempt`,
`many`, `sepBy`, `tryCatch`, etc.  It is the most ergonomic option in
the standard library.

We chose **not** to depend on it for three reasons:

1. **`Internal` is in the namespace.** The Lean team has not committed
   to API stability for anything under `Std.Internal.*`.
2. **`String.Pos` is now dependently typed** (`String → Type`) as of
   Lean 4.30, and the `Sigma String.Pos` machinery `Std.Internal.Parsec`
   uses changed shape several times in 2024–2026. Generated code that
   uses it tends to break across Lean upgrades.
3. The combinators we actually need are very small (`pure`, `bind`,
   `<|>`, `many`, `sepBy`, three or four token-class predicates).
   Re-implementing them takes ~100 lines and isolates us from churn
   in `Std.Internal.*`.

### 2.3 Why we *don't* use third-party combinator libraries

The most polished one is `fgdorais/lean4-parser`. It pulls in
`batteries` and `lean4-unicode-basic` as transitive Lake
dependencies. For a tool like BNFC where users routinely generate
parsers for their own languages and ship them, every Lake dependency
becomes a new constraint on toolchain compatibility. A self-contained
output is much friendlier.

### 2.4 Why we *don't* use Lean's `syntax` / `macro` system

Lean's built-in parser framework parses Lean source files at
elaboration time. It is not a general-purpose runtime parser
(though clever DSLs sometimes coax it into one). BNFC users
overwhelmingly want a tool that parses *external input strings* —
their compiler frontends do `getContents >>= parse` on a `.foo`
file, not `runMacro` on an embedded Lean term. So `syntax`/`macro`
is the wrong abstraction.

### 2.5 What we *do*: hand-rolled recursive descent + tiny runtime

The runtime in `ParserRuntime.lean` defines:

```lean
abbrev Parser (α : Type) := List Token → Except ParseError (α × List Token)
```

— i.e., a function from a token list to an `Except`. The token list
is materialised once by the lexer; the parser is a plain recursive
function over `List Token`. This is dirt-simple, terminates obviously
(input shrinks), and works on every Lean 4 version we tested.

The lexer (`LexLANG.lean`) operates over `List Char` for the same
reason: `String.Pos` is an unstable target. Converting `input.toList`
once is O(n) and cheap relative to parsing.

## 3. Architectural choices

### 3.1 File-naming convention

Mirrors `BNFC.Backend.Haskell.HsOpts`: `Abs`, `Lex`, `Par`, `Print`,
`Test`, all suffixed with the `lang` field of `SharedOptions` in
CamelCase. This keeps Lean output discoverable for users who already
know other BNFC backends.

### 3.2 AST representation

- One `inductive` per BNFC category (`isDataCat . normCat`).
- Wrapped in a single `mutual ... end` block so that constructors
  may freely reference any other category.
- Token categories (`Ident`, user `token` pragmas) emitted as
  `abbrev Foo := String`. Built-in literal categories use native Lean
  types: `Integer → Int`, `Double → Float`, `String → String`,
  `Char → Char`.
- The whole module is wrapped in `namespace AbsLANG` so callers can
  `open AbsLANG` and write unqualified constructor names.
- We **do not** emit `deriving Inhabited` because Lean's auto-deriver
  fails for many real grammars (e.g., `Stmt` whose every constructor
  takes a non-trivially-inhabited subtree). Only `deriving Repr` is
  emitted; users can add `Inhabited` themselves where it makes sense.
- We **do not** encode position information in the AST. This matches
  the OCaml backend's default behaviour. Adding it later is
  straightforward (mirror the Haskell `--positions=range` machinery).

### 3.3 Precedence climbing

BNFC's coercion mechanism (`coercions Exp 2` plus rules like
`EAdd. Exp ::= Exp "+" Exp1`) is naturally a precedence-climbing
recursive-descent grammar. For each base category `C` with precedences
`[0..max]`, we emit `pC0`, `pC1`, …, `pCmax` (with `pC0` aliased to
`pC`). The transformation is the textbook one:

- Rules whose RHS *starts* with a non-terminal at the same precedence
  are **left-recursive** → fold into a `where loop` that iteratively
  builds up the LHS.
- Rules with a different shape are **non-recursive alternatives** →
  emit as direct `do { let x ← p; return Ctor x }` blocks joined by
  `<|>`.
- A pure coercion `_. Cn ::= Cm` (n < m, no terminals) → delegate to
  `pCm`.
- A coercion *with* terminals (`_. Cn ::= "(" C ")"`) → match the
  terminals and return the inner argument unwrapped (no constructor
  exists for `_`).

The whole parser group is wrapped in `mutual ... end` so the levels
can call each other freely.

### 3.4 List rules

BNFC treats `[C]` as a separate category with three canonical rules:
empty (`[]`), singleton (`(:[])`), and cons (`(:)`). We detect the
declared separator (if any) by inspecting the cons rule's RHS and pick
one of `Parser.many` / `Parser.many1` / `Parser.sepBy` /
`Parser.sepBy1`. List parsers are placed *inside* the `mutual` block
together with the value-category parsers, which avoids forward-
reference errors when a category recurses through a list.

### 3.5 Pretty-printer

Mirrors the parser's structure: one `partial def` per category in a
`mutual` block. Each constructor is rendered by interleaving its
sub-printer outputs with the literal terminals from the original rule
(`String.intercalate " " […]`). No layout / indentation logic runs
yet; users wanting nicer output customise `prSep` or write their own.
List printers are also emitted inside the same `mutual` block so they
can be called from value-category arms.

### 3.6 Lexer

Skip whitespace and grammar-declared comments, then try in order:

1. integer / float literals (with optional fractional part, manually
   converted to `Float` since `Lean 4.30` has neither `Int.toFloat`
   nor `String.toFloat?`),
2. string and character literals (with `\n \t \r \\ \" \'` escapes),
3. identifier-shaped lexemes (reserved words promoted to keyword
   tokens),
4. punctuation symbols, sorted by descending length so `==` is
   preferred over `=`.

The runtime token type carries source positions (`line`, `col`) so
parser errors can pinpoint where things broke.

### 3.7 Generated `lean-toolchain`

elan refuses to interpret a toolchain file with a leading comment.
The base `writeFiles` always prepends a BNFC stamp using the
backend-supplied comment-prefix function. To preserve that
invariant for everything else, I added one tiny escape hatch in
`BNFC.Backend.Base.writeFiles`: if the comment function returns the
empty string, the file is emitted *without* the stamp. The Lean
backend uses `const ""` for the toolchain file only.

This change is the only modification we made to non-Lean BNFC code.
It is backwards-compatible (all existing backends use a
non-empty-stripping comment function).

## 4. Known limitations and follow-up work

### 4.1 User-defined `token` pragmas (regex tokens)

Currently a no-op. If a grammar has `token Foo letter (letter | digit)*`,
the generated `LexLANG.lean` contains a comment warning the user that
those tokens won't be recognised. The infrastructure is in place
(token kind `userTok cat lexeme`, parser combinator `expectUserTok`),
but the regex-to-Lean compiler is missing.

I started writing one (`RegToLean.hs`) but reverted it because
implementing `Reg → (List Char → Option (List Char × String))`
correctly across all `Reg` constructors (`RAlt`, `RSeq`, `RStar`,
`RMinus`, character classes, `RDigit`, `RLetter`, `RUpper`, `RLower`,
`RAny`, …) needed more design than I wanted to bake in on first cut.
The right approach is probably a small NFA representation; recursion
on `Reg` directly is fine for `RChar`/`RAlts`/`RSeq` but ugly for
`RStar` because greedy matching has to be careful about progress.

### 4.2 Layout pragmas (`layout`, `layout stop`, `layout toplevel`)

Not implemented. The Haskell backend has a 200+ line layout resolver
in `BNFC.Backend.Haskell.CFtoLayout`; we'd need to port the same
algorithm. No grammar in the BNFC test suite actually uses layout
pragmas, so this is low priority but real work.

### 4.3 `--positions=start|range` flag

Not wired up for the Lean backend. The flag currently only applies to
Haskell targets (see `specificOptions` in `BNFC/Options.hs`). To add
positional ASTs we'd need to:

1. Make every `inductive` constructor optionally take a `BNFC.Position`
   prefix.
2. Thread positions through the lexer's token records (already
   present in the runtime!) into the parser actions.
3. Provide a `getPosition` parser combinator.

### 4.4 Internal rules (`internal Foo. Cat ::= ...`)

We filter on `isParsable` so internal rules don't appear in the parser.
But the AST will still expose them as constructors. The Haskell
backend emits internal-only constructors that don't appear in any
Happy production but *do* appear in `Abs.hs`. We do the same. If a
user wants to construct one programmatically they can; they just
can't parse one.

### 4.5 `define` rules

`FunDef` pragmas are currently *ignored*. The OCaml backend translates
them to `let f x = …` definitions; we should do the equivalent
(`def f (x : ...) := …`) but that needs a small expression-tree
walker.

### 4.6 GLR / ambiguous grammars

Recursive descent can't handle ambiguous grammars naturally. If a
grammar truly has multiple valid parses, only the first one tried
will succeed. BNFC has historically had a Happy GLR mode for
exploring ambiguity; that is out of scope for this backend.

### 4.7 Error recovery

The current parser fails fast on the first syntax error and reports
position + expected token. There is no error-recovery mode (e.g.,
"skip until next `;` and try again"). For a teaching-grade compiler
the current behaviour is fine; for a production frontend it is not.

### 4.8 Performance

Parser generators like Happy/Bison produce parse tables that run in
linear time. Recursive descent with backtracking can be exponential
on pathological inputs. In practice, grammars BNFC users write are
LL-ish enough that this never happens, but if someone writes a
heavily-ambiguous left-factored grammar they may notice slowness.

`many` and `sepBy` are written with `partial def` and accumulate via
`List.cons`, so they reverse the accumulator at the end — no
quadratic blow-up. The whole parser allocates a fair number of
intermediate `Except` values; if profiling shows this is hot we can
specialise the monad.

### 4.9 Char/String escape sequences

The lexer recognises `\n \t \r \\ \" \'`. Other common escapes
(`\xNN`, `\uNNNN`, octal) are *not* parsed; they pass through
unchanged. Real-world languages will need this; it's a 30-line
addition in `matchStringLit`/`matchCharLit`.

### 4.10 Lean version drift

Pinned toolchain is `leanprover/lean4:v4.30.0`. The generated code
relies on:

- `String.ofList`, `String.toInt?`, `String.toNat?`, `String.intercalate`,
- `Char.isAlpha`, `Char.isDigit`, `Char.isAlphanum`, `Char.isWhitespace`,
- `Nat.toUInt64`, `UInt64.toFloat`,
- `List`, `List.contains`, `List.reverse`, `List.length`, `List.map`,
- `Except`, `Sum`,
- `Repr` deriving.

None of those are unstable APIs at present, but each Lean release
sometimes deprecates / renames things (e.g., `String.Iterator` →
`String.Legacy.Iterator` in 4.30). When bumping the pin, do a
`lake clean && lake build` on a generated project; warnings caught
during that round-trip are usually low-effort to fix in the
generator.

## 5. How to test changes

### 5.1 Unit tests

`source/test/BNFC/Backend/LeanSpec.hs` runs `makeLean` on a calc
grammar and asserts that the right files are generated and that key
strings appear in their contents. Add a new case here for any
new generator behaviour.

```bash
cd source && cabal test
```

### 5.2 End-to-end smoke

The fastest sanity check is to compile a generated project with
`lake` (which is in PATH if elan is installed). `tmp/` is a
gitignored scratch directory:

```bash
cabal run bnfc -- --lean -o ../tmp/lean-test ../tmp/lean-test/Calc.cf
cd ../tmp/lean-test
lake clean && lake build
echo "1 + 2 * 3" | ./.lake/build/bin/testCalc
```

Test grammars that have proven informative:

- `Calc.cf` — basic precedence, arithmetic
- `Lang.cf` (in `tmp/lean-test2/`) — identifiers, lists with
  separators, comments, mixed literal kinds

When you change the parser generator or the runtime, run *both*.

### 5.3 Cross-checking with the Haskell backend

A nice check is to also run `bnfc --haskell` on the same grammar and
manually compare ASTs. Differences usually mean the Lean parser is
either too strict or wrongly factoring a left-recursive rule.

## 6. Code layout

| File                          | Lines | Purpose                                                     |
| ----------------------------- | ----- | ----------------------------------------------------------- |
| `Lean.hs`                     | ~110  | Top-level orchestrator: emits all files + Makefile + Lake   |
| `Lean/LeanUtil.hs`            | ~110  | File-name conventions, identifier sanitising, Cat → Lean    |
| `Lean/CFtoLeanAbs.hs`         | ~80   | Generates the AST `inductive`s                              |
| `Lean/CFtoLeanLex.hs`         | ~310  | Generates the lexer (longest-match over `List Char`)        |
| `Lean/CFtoLeanPar.hs`         | ~360  | Generates the recursive-descent parser w/ precedence climb  |
| `Lean/CFtoLeanPrinter.hs`     | ~155  | Generates the pretty-printer                                |
| `Lean/CFtoLeanRuntime.hs`     | ~165  | Embeds the runtime — *the same string for every grammar*    |
| `Lean/CFtoLeanTest.hs`        | ~45   | Generates the `Main`/CLI driver                             |

If you add a new submodule, register it in `BNFC.cabal` under
`exposed-modules` *and* in the `Lean/` section of `Lean.hs` if it
emits a file.

## 7. Sharp edges to remember

1. **`Lean 4.30` removed `String.Pos` as a plain type.** Anything
   touching `String.Pos`/`String.Iterator` will trigger deprecation
   warnings or hard errors. The lexer was rewritten to operate on
   `List Char` for this reason; do not undo that without verifying
   the new code compiles on at least three Lean versions.

2. **`String.toFloat?` does not exist.** We synthesise a `Float` from
   integer + fractional `Nat`s and `Nat.toUInt64.toFloat`. Don't try
   to use `String.toFloat?` — it's been promised but not delivered.

3. **`deriving Inhabited` for mutual `inductive`s often fails.** The
   auto-deriver needs to find a witness for *every* type in the
   mutual block, simultaneously. Real grammars routinely have
   `Stmt`/`Exp`/etc. that don't satisfy Lean's heuristic. Stick to
   `deriving Repr` and let users add `Inhabited` instances by hand
   if they need them.

4. **`let mut` requires `do` notation.** A plain `def` cannot use
   `let mut`. If you see "unexpected token 'mut'", you have a
   non-`do` definition trying to mutate. Refactor to recursion.

5. **`namespace M ... end M`** must wrap the entire AST, otherwise
   `open M` from another module fails with "unknown namespace M".
   The orchestrator depends on this and will not catch the mistake
   at code-generation time.

6. **`<|>` requires the `OrElse` instance to be visible.** It is
   declared in `ParserRuntime.lean`. If you change the runtime
   namespace, update the `open` lines in the generated parser.

7. **The `lean-toolchain` file must not start with anything other
   than a toolchain identifier** — see the escape hatch in
   `Backend/Base.hs`.

## 8. Suggested order of attack for the next iteration

If a future maintainer wants to push the backend forward, this is
roughly the order I'd recommend:

1. Implement `Reg → Lean` for user-defined token pragmas. Easiest
   win for grammars that aren't covered today.
2. Wire up `--positions=start|range`. Token positions are already
   threaded through the lexer; surfacing them in the AST is purely
   plumbing.
3. Add layout support (port `CFtoLayout.hs` logic). Gates a small
   but real set of grammars (Haskell-style indentation languages).
4. Optional: explore swapping the generated runtime for
   `Std.Internal.Parsec`. Worth doing once the standard library
   declares it stable, since it's a more battle-tested codebase.

Each step is independent; pick whichever gates the grammars you
actually care about.
