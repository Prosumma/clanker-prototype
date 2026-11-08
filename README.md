# Clanker prototype

A throwaway Haskell prototype for kicking the tires on the design in [`DESIGN.md`](DESIGN.md). What's open (undecided, deferred, unbuilt, or limited) is in [`OPEN.md`](OPEN.md), which is definitive. The real compiler will be written in Rust; nothing here is meant to last. Optimize for speed of change, not polish.

## Layout

- `examples/` — hand-written Clanker programs (`.clk`), in canonical form. They're the test suite.
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

Not yet: refinements are erased in the checker, open structural records, constraints on a type's parameters at use sites, and instances checked against their class. [`OPEN.md`](OPEN.md) has them, as O-26, O-19, O-18 and O-14.

## What effect checking checks

Every function type carries an effect row, and a body may perform only what its row allows (DESIGN §3):

- **Calls.** A call's effects must be covered by those allowed where it's made: the function's `effects` clause, or, in a function value, its type's row. A row variable (`map`'s `E`) takes the effects allowed at the call, so the function passed in may perform them too.
- **Rows** unify Koka-style, with scoped labels, so a row can hold two `Fail`s. Type arguments unify (`Fail[E]` picks up `CountError` from what `run` performs), which settles the type parameters only effects determine, like `attempt`'s error type. A constraint still on an unknown type is now an error.
- **Function values.** A named function used as a value has an open row, so it can be passed where more is allowed. An effect parameter naming its own argument widens to `any`.
- **Handlers** add their effects to the handled code's row, with `any` parameters. A handler must have a clause for every operation of each effect it handles. Clause bodies and `resume` run with the effects allowed outside. `resume` can only be called, at most once on any path, and never from a function value. A generic operation's own type parameters and row variables are rigid in its clause (`on gen() => resume("x")` is an error for `gen[A]() -> A`, and a clause can't run a callback whose effects are the operation's `E`), and can't escape it: by levels, nothing made outside the clause may be bound to a type mentioning them, a function type ending in such a row included. No user handler may take `Stm`; only `atomically` handles it.
- **Tasks** (`run_concurrently[E: RootEffects]`) perform only root effects, the ones the runtime handles in every thread. A function passing its own row there declares it `RootEffects`, and such a function is only called directly. Its row is checked after the arguments, closed, so it's what the tasks perform.
- **Local state** (`with_state`, only called directly). A cell's contents can't be a refined type. Each call gets a fresh rigid region `R`, younger than everything made before it, so by levels nothing made outside can hold its cell. Its result and remaining effects can't mention `R` either, including a function type's `Local[R]`. The body must be a lambda at the call. `Local[R]` is matched by region rather than by being innermost, and a call whose `Local` region isn't known yet (`get`, `put`, a helper given a cell) checks its effect after its arguments have fixed it. A region's `Local` may be performed more than once in one row. No user handler may take `Local`, `run_concurrently`'s tasks can't perform it, and specs may `get` where `Local` is granted.
- **Effect parameters** must be written out (`Fs[read: any]`, not `Fs`), and each one is a literal, `any`, or the name of one of the function's parameters, of the declared type. The checker rejects `any` where only a specific value is granted, and two literals that differ. Everything else is left to the verifier.
- **`main`** may perform only the root effects the runtime handles.

Not yet: how effect parameters that name values are compared ([`OPEN.md`](OPEN.md) O-4), and row unification for `Local` (O-28).

## What the interpreter does

- **Evaluation** is eager and left to right. Proof code is erased.
- **Algebraic effects.** Evaluation suspends at each effect operation with its continuation. A `handle` interprets the operations it covers, and `resume` continues, so handlers can do work after resuming (`collect_traces` in `06_trace.clk`). Built-in effects (`Console`, `Args`, `Log`) are handled at the top level for `main`.
- **STM.** `atomically` runs a transaction under one global lock with buffered writes. `retry` rolls back and waits for another commit. `run_concurrently` uses real threads.
- **Literal types.** The checker records each integer literal's type, so `UInt64` and `Wrapping` arithmetic are exact, and fixed-width overflow is a runtime error, as a backstop to the verifier. A literal whose type is a generic type variable is a plain integer, promoted when it meets a float or a fixed-width value.
- **Doc examples** (`clanker test`) become functions in a generated module that imports everything the original module sees. They're type-checked with the program, and errors point at the doc-comment line.

Not yet: full grapheme segmentation, some primitives (`decode_json`, `Http`, `Db`), and instance dispatch. [`OPEN.md`](OPEN.md) has them, as O-24, O-23 and O-17.

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
- **Local state** (`with_state`, DESIGN §3). A cell is a TVar to the verifier: `get` and `put` are `read` and `write` on the same heap, and a new cell is distinct from the others made in the function. The body, a lambda at the call, is verified in place. A call whose effects are only `Local[...]`, with each region's cell known, forgets only those cells: frames for cells. Any other effectful call, one that performs anything but `Stm` included, forgets every TVar and cell.
- **Handler clauses.** Each operation clause is verified, assuming the operation's parameter refinements and precondition. `resume`'s argument must satisfy the operation's result type and postcondition (with `old(...)` the state at the operation). A handler can make a computation that doesn't return (`fail`) return, so code after a `handle` is live.

Not yet, all in [`OPEN.md`](OPEN.md): frame conditions for TVars (O-9), instances checked against their class (O-14), verified doc examples (O-25), `assume` and `axiom` (O-38), `unsafe` and FFI (O-39), class laws as proof obligations (O-40), and the limitations O-27, O-29 to O-33, and O-37. The two trusted assumptions are `Ord` totality (O-34) and `atomically`'s result (O-35).

