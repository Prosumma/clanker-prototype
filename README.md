# Clanker prototype

A throwaway Haskell prototype for kicking the tires on the design in [`DESIGN.md`](DESIGN.md). The real compiler will be written in Rust; nothing here is meant to last. Optimize for speed of change, not polish.

## Layout

- `examples/` — hand-written Clanker programs (`.clk`), in canonical form. They're the test suite. `examples/NOTES.md` records what writing them revealed about the design.
- `std/` — the standard library, in Clanker: enough of it for the examples. Real bodies where they're easy (most of `Std.List`, `Std.Fail`); `primitive` declarations for what the runtime provides.
- `src/Clanker/` — compiler stages:
  - `Syntax` — the syntax tree, including comments and literal spellings, so formatting round-trips.
  - `Parser` — megaparsec. Tracks whether newlines are significant (statements) or whitespace (inside brackets).
  - `Pretty` — the canonical formatter (DESIGN §6.1).
  - `Load` — finds modules (the standard library under `std/`) and the prelude.
  - `Types` — the checker's internal types.
  - `Check` — the type checker.
  - `Match` — exhaustiveness and the wildcard-dispatch rule.
  - `Eval` — the interpreter.
  - `Examples` — doc-comment examples, compiled into a generated module.
  - `Driver` — load, check, run, and verify; shared by the CLI and the tests.
  - `Verify` — the verifier: symbolic execution to proof obligations.
  - `Smt` — SMT-LIB terms, and running Z3.
- `app/` — the `clanker` command-line tool.
- `test/` — the test suite:
  - every example and standard-library module parses, formats to itself, and re-parses to the same tree;
  - every example type-checks, and its doc examples pass;
  - the two programs with a `main` run, with their output checked;
  - a deliberately wrong doc example is reported as failing;
  - every example and standard-library module verifies, with every obligation proved, and so does every program in `test/verified/` (cases that once failed for the wrong reason);
  - how many obligations each proves, and how many doc examples each has, match `test/counts.txt`, so a change that silently stops generating them shows up;
  - each program in `test/unverified/` has one bug the verifier must refute: the failing obligations are exactly those at the lines `-- line:` gives, each refuted (not "gave up") and described by the `-- expect:` line;
  - programs that must be rejected: by the parser (inline in `test/Main.hs`) and by the checker (`test/reject/`, whose first error must match `-- expect:` at `-- line:`; line 0 is an error about the whole file);
  - visibility across modules (`test/visibility/`): programs importing the library `Vis/Bank.clk`. Those with `-- expect:` must be rejected as above, unless named `unverified_*`, which must be refuted as in `test/unverified/`; the rest must verify, and so must the library.

## Build and run

```sh
cabal build all --enable-tests
cabal run clanker -- fmt examples/08_calculator.clk          # print canonical form
cabal run clanker -- fmt --write examples/08_calculator.clk  # rewrite in place
cabal run clanker -- parse examples/08_calculator.clk        # dump the syntax tree
cabal run clanker -- check examples/08_calculator.clk        # type-check (std from ./std or $CLANKER_STD)
cabal run clanker -- test examples/04_text.clk               # run the doc examples
cabal run clanker -- run examples/07_ledger.clk              # run main
cabal run clanker -- run examples/05_wordcount.clk FILE...   # with arguments
cabal run clanker -- verify examples/08_calculator.clk       # prove every obligation
cabal run clanker -- verify -v examples/01_transfer.clk      # ... listing each one
cabal test
```

Verification needs `z3` on `PATH`. `CLANKER_DUMP=dir` writes every solver script to `dir`.

## Plan

1. ~~Parser and canonical formatter.~~ Done: covers the whole surface syntax used by the examples.
2. ~~Type checker.~~ Done; see below for what it covers.
3. ~~Tree-walking interpreter.~~ Done; see below.
4. ~~Verifier.~~ Done; see below.
5. ~~Effect rows and handlers, including parameterized effects.~~ Done; see below.

Out of scope: higher-kinded types, code generation, packages, the language server, incremental compilation.

## What the type checker checks

- Imports and name resolution, including the prelude. A name clash (two imports, or an import and an own declaration) is an error that suggests a rename, `import Land.Plots (area as plot_area)`, and a rename is allowed only to resolve one. A program's own modules are files under its root, where the entry file's module name starts (`Bank.Accounts` is `Bank/Accounts.clk`). Import cycles through a module with functions, lemmas, constants, or instances are rejected, and only std's files may declare `Std.*`. `verify` verifies every module of the program, not just the entry.
- **Visibility** (DESIGN §6). Only `public` declarations can be imported. Outside its module, a record's private fields can't be read, and a record or newtype with anything private can't be built, matched, or `with`-updated. A public declaration's signature, contract, and the refinements in them name only public things (nor build, match, or update a type with private fields), and a public field's refinement only public fields. `deriving (Decode)` is rejected on a public type with anything private. A class without methods (`Decode`, `IntLiteral`, `Add`, ...) can't be instantiated by hand: its instances come from `deriving` or std's `primitive instance`s, and only std declares primitives. Overlapping instances are rejected. A derived `Display` writes private fields as `..`. Doc examples see private names.
- Records, variants, newtypes, aliases, structural records, tuples, and generics.
- Typeclass constraints, instances, superclasses, and deriving.
- Argument labels (DESIGN §6) and no shadowing.
- Exhaustive matches, with an example of an unhandled value, and the wildcard-dispatch rule.
- Discarded results.
- Integer literal types and their ranges.
- Every spec (refinement, `requires`, `ensures`) is a well-typed `Bool`, and pure: specs and proof code (`proof`, `assert`, `calc`, lemmas) perform nothing, except that in an `Stm` function they may `read` TVars.
- Labels: two parameters whose types are type variables count as sharing a type.
- **TVars:** a TVar's refinement is part of its type (`TVar[Cents]` isn't `TVar[Int]`), so it must be named by an alias. A TVar's contents can't hold a TVar, directly, through other values, or in a function value.
- **Invariant types** own their TVars (DESIGN §5). Only their module builds one, and every TVar field must be a `new_tvar(...)`. Nothing takes one apart with a pattern or copies one with `with`. A TVar field is named only as what `read` or `write` acts on, and outside the module it can only be read.
- Effects; see the next section.

Not yet:

- **Refinements are erased,** except inside `TVar`. `Cents` is `Int` to the checker. The verifier proves them.
- Open structural records (`| r`) aren't supported.
- Constraints on a type's parameters (`Wrapping[I: FixedWidth]`) aren't checked where the type is used.
- Instance members aren't checked against their class's signatures.

## What effect checking checks

Every function type carries an effect row, and a body may perform only what its row allows (DESIGN §3):

- **Calls.** A call's effects must be covered by those allowed where it's made: the function's `effects` clause, or, in a function value, its type's row. A row variable (`map`'s `E`) takes the effects allowed at the call, so the function passed in may perform them too.
- **Rows** unify Koka-style, with scoped labels, so a row can hold two `Fail`s. Type arguments unify (`Fail[E]` picks up `CountError` from what `run` performs), which settles the type parameters only effects determine, like `attempt`'s error type. A constraint still on an unknown type is now an error.
- **Function values.** A named function used as a value has an open row, so it can be passed where more is allowed. An effect parameter naming its own argument widens to `any`.
- **Handlers** add their effects to the handled code's row, with `any` parameters. A handler must have a clause for every operation of each effect it handles. Clause bodies and `resume` run with the effects allowed outside. `resume` can only be called, at most once on any path, and never from a function value. A generic operation's own type parameters are rigid in its clause (`on gen() => resume("x")` is an error for `gen[A]() -> A`), and can't escape it: by levels, nothing made outside the clause may be bound to a type mentioning them. No user handler may take `Stm`; only `atomically` handles it.
- **Effect parameters** must be written out (`Fs[read: any]`, not `Fs`), and each one is a literal, `any`, or the name of one of the function's parameters, of the declared type. The checker rejects `any` where only a specific value is granted, and two literals that differ. Everything else is left to the verifier.
- **`main`** may perform only the root effects the runtime handles.

Not yet:

- When two function types are unified, effect parameters that name values are compared by spelling.
- Effect handlers installed around `run_concurrently` don't reach its tasks at runtime (see the interpreter), though the checker allows it.

## What the interpreter does

- **Evaluation** is eager and left to right. Proof code is erased.
- **Algebraic effects.** Evaluation suspends at each effect operation with its continuation. A `handle` interprets the operations it covers, and `resume` continues, so handlers can do work after resuming (`collect_traces` in `06_trace.clk`). Built-in effects (`Console`, `Args`, `Log`) are handled at the top level for `main`.
- **STM.** `atomically` runs a transaction under one global lock with buffered writes. `retry` rolls back and waits for another commit. `run_concurrently` uses real threads.
- **Literal types.** The checker records each integer literal's type, so `UInt64` and `Wrapping` arithmetic are exact, and fixed-width overflow is a runtime error, as a backstop to the verifier. A literal whose type is a generic type variable is a plain integer, promoted when it meets a float or a fixed-width value.
- **Doc examples** (`clanker test`) become functions in a generated module that imports everything the original module sees. They're type-checked with the program, and errors point at the doc-comment line.

Not yet:

- **Grapheme segmentation is approximate:** combining marks, ZWJ sequences, emoji modifiers, variation selectors, and regional-indicator pairs. Full UAX #29 isn't implemented.
- **Some primitives aren't implemented:** `decode_json` (it needs the target type at runtime), and the `Http` and `Db` effects. `10_order_sync.clk` type-checks but can't run.
- **Instance members with bodies aren't dispatched at runtime.** Class methods work for the built-in instances, by the shape of the value.
- **Effect handlers installed around `run_concurrently` don't reach into its threads.** The tasks only see the built-in effects.

## What the verifier proves

`clanker verify FILE` executes each function symbolically and sends every proof obligation to Z3 separately, with a fixed resource budget. The obligations:

- **Refinements** wherever a value flows into a refined type: arguments, results, record and constructor fields, `let` annotations, and values written to a refined `TVar`.
- **`requires`** at every call, and **`ensures`** wherever the body returns normally. A call to `fail` or `retry` doesn't return, so it owes no postcondition.
- **Arithmetic:** nonzero divisors, and no overflow in fixed-width arithmetic.
- **Termination:** `decreases` measures (integers, or lexicographic tuples of them, which the checker requires) at every call within a recursive group. A callee's postcondition is available when proving its measure goes down, as the calculator's parser needs. Without a measure, a function calling only itself must recurse on a part of a parameter that a pattern took apart, or on a value rebuilt from such parts, and on the same parameter at every call. Any other recursion without measures fails, as does a group member used as a value inside its group. Calls in proof code (`calc`, `proof`, `assert`) count.
- **Proof code:** `assert`, `calc` steps, lemma preconditions and postconditions, and `unreachable()`.
- **Well-formed specs:** a call in a `requires`, `ensures`, refinement (alias, field, parameter, result, `let`), invariant or `decreases` owes its precondition and its parameters' refinements. Each declaration is checked once where it's declared (reported as `type X` or `invariant n`).
- **Function values** given where a function type is declared (an argument, a constructor field, a record update, an annotated `let`) may need no more of their arguments than the type promises, and must deliver its result refinement. A lambda is checked directly. A function with a precondition or a refined parameter can't be let out as a value any other way. Calling a function-typed parameter owes its parameter refinements and its effects, and gives its result refinement.
- **Constants and instance members** are verified like functions.
- A record update rechecks every field's refinement.

How the proofs work:

- **Pure calls** become solver functions. Their contracts apply wherever they appear, and their definitions unfold one level, both only where the callee may be called: under its parameters' refinements and its precondition. `unfold f` adds a level, and calls on constructor values unfold further.
- **Type-variable refinements** (`fold`'s `B` as `Cents`) are assumed of a result only where every input of that type is checked and the callee can't produce one otherwise, through its effects or its class constraints (`negate`, `-`, literals). DESIGN §2 has the rule.
- **A TVar's refined contents** (`A := Cents` from a `TVar[Cents]` argument) are owed by every `A` the caller hands a generic function. An `A` that could get in unchecked (in a `List[A]`, a callback's argument, a returned function's parameter) makes the call unprovable.
- **Equality is identity**, and `<=` total, only for types whose instances make them so: primitives other than floats, multisets, and types with derived instances over such fields. A type variable gets `Ord`'s totality and nothing else.
- **Facts stay scoped:** what a function value's body, a handled computation, or a handler clause establishes isn't known afterwards.
- **Calls with effects** return an unknown value that satisfies the callee's postcondition.
- **Built-in theory** includes datatypes for every record and variant, multisets as arrays of counts, sign facts for products, totality of `<=` on `Ord` types, `all`/`contains`, and a list's head and tail being in it.
- **A failure** comes with a counterexample, and a hint to `unfold` when a definition ran out of fuel. In that case the model is only a "possible" counterexample.
- An obligation that's true by construction counts as proved, so the counts show every check that ran.

With effects (step 5):

- **Effect parameters.** A call's effects must stay within those granted: `read_bytes(secrets)` under `Fs[read: config]` must prove `secrets == config`. An operation's precondition can name its effect's parameters: `get(url)` under `Http[host: "orders.internal"]` must prove `url.host == "orders.internal"`.
- **TVar state** is an array per element type, threaded through the body. `read` selects, and the value has the TVar's refinement. `write` stores, and owes the value the refinement. A call that might run transactional code (an `Stm` function, a row variable, a function value, another effect's operation) replaces the arrays with unknown ones, and its postcondition says what's known afterwards. Both branches of an `if`, `match`, `and`, or `or` start from the same state, and merge. `old(...)` reads the state on entry. TVars created by `new_tvar` are distinct.
- **Invariants** (with ownership, DESIGN §5): a new value must satisfy its invariant. Code that writes a value's TVars must re-establish its invariant before it returns or commits, and before anything that might not return here (an operation other than `Stm`'s, or a call that may perform one). A write is attributed to the value it names (`write(x.f, ...)`), from the syntax. An `Stm` function's result of an invariant type must satisfy the invariant. Values it didn't write keep theirs, so an `Stm` function may assume its parameters', a transaction those of the values in scope, and anything may re-assume untouched values' invariants after a call. A call to an `Stm` function owes the invariant of any argument that might have been written. A transaction is any function value that may perform `Stm` where nothing around it may. Other function values, and handler clauses, run at an unknown point, so they assume nothing.
- **Other modules' definitions.** A function or constant from another module is known by its contract or declared type, and by its definition only if it's public and the definition names only public things (DESIGN §4). Those are recorded by the checker.
- **Handler clauses.** Each operation clause is verified, assuming the operation's parameter refinements and precondition. `resume`'s argument must satisfy the operation's result type and postcondition (with `old(...)` the state at the operation). A handler can make a computation that doesn't return (`fail`) return, so code after a `handle` is live.

Not yet:

- **No frame conditions.** After an `Stm` call, a caller knows only what the callee's postcondition says about TVars (DESIGN open question 8). Inside an invariant type's module, a function holding two values that calls a helper on one must still re-establish the other's invariant if it wrote it.
- **A new TVar is known to be distinct from other new ones,** not from TVars that existed before.
- **Refinements inside a parameter's type arguments aren't assumed:** `amounts: List[Cents]` doesn't make the elements `Cents`. (So they aren't owed either, and nothing relies on them.)
- **A `handle` expression's value is unknown**, even for `handle 5 on ...`.
- **Structural termination** is for a function calling only itself, on one parameter; mutual recursion, and recursion that shrinks different parameters by turns (`merge`), need measures.
- **Class method signatures' refinements** aren't checked for well-formedness.
- **Class methods can't have `requires` or `ensures` yet.** Every call would assume them, and instances aren't checked against them. Recursion through a class method (a generic function calling a method whose instance calls it back) is rejected, since its termination isn't checked.
- Instance members are verified but not yet checked against their class's signatures or dispatched at runtime. When they are, members must be matched to methods by the method's declared name: a member named after a renamed method's local name (`g_size` for `size as g_size`) is accepted today, and the dispatch-cycle check doesn't see it.
- **Floats and strings are uninterpreted.** Facts about them come only from specs.
- **Class laws** aren't checked, and aren't used except for one: a type variable's `<=` is assumed total under `Ord`. For a hand-written `Ord` instance, that rests on a law nothing proves, so it belongs in the trust ledger. (It can't go wrong at runtime yet, since instance members aren't dispatched.)
- **`atomically`** is trusted to return its transaction's result, so a refinement passes through it (`let r: Cents = atomically(function() => read(b))`).
- **Doc examples aren't verified,** only run (`clanker test`).

