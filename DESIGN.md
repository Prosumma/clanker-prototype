# Clanker — Design Notes

> Status: early sketch (started 2026-11-07). "Clanker" is a code name; a real name is still to be chosen.
>
> Clanker is a language *for* LLMs, designed *by* an LLM: Claude makes the design decisions and records them here, and Gregory reviews them. The design is tested against the example programs in [`examples/`](examples/).

## Thesis

A general-purpose, compiled programming language optimized for code written by LLMs, with the goal of **minimizing the need for human review**.

The organizing principle: **humans review the specification; the machine checks the implementation.** If types, contracts, and effect signatures are expressive enough — and the compiler proves that implementations satisfy them — then most of a change is machine-verified implementation, and human attention is reserved for:

1. **Specs** — are the types, refinements, pre/postconditions, and invariants what we actually want?
2. **Authority** — what effects is this code permitted to perform?
3. **Trust escapes** — where was the checker told to believe something it didn't prove?

Every feature should either shrink that review surface or make it easier to read.

## Goals

- **Broad domain.** Backend services, CLIs, GUIs, and other general-purpose work. It does not need to beat Rust on performance, but it should be fast enough that no one reaches for something else on speed grounds.
- **Compiled** to native code.
- **Readable over writable.** LLMs don't care about sugar. Verbosity is acceptable where it makes code easier to read; COBOL-level verbosity is not.
- **Local reasoning.** Any function should be understandable from its file, its signature, and the signatures it calls — whether the reader is a human reviewer or an LLM with limited context.

## Non-goals

- Being pleasant to write by hand at speed.
- Laziness, point-free style, or user-defined notation.
- Beating Rust/C++ on raw performance.

---

## 1. Core semantics

- **Pure functional.** No mutation or side effects outside the effect system.
- **Eager (strict) evaluation.** Lazy evaluation makes memory and time use hard to predict for both reviewers and LLMs.
- **Total by default.** Functions must provably terminate. Non-termination is an effect (`Diverge`) that must be declared.
- **No null, no exceptions.** Failure is expressed with `Result`/`Option` or as an effect (`Fail[E]`).
- **No silent overflow.** There are two families of integer types, distinct from each other:
  - `Int` is arbitrary-precision and the default type for integer literals. Small values are stored unboxed (as Lean does), so it's cheap in the common case.
  - Fixed-width `Int8`…`Int64` and `UInt8`…`UInt64`. Ordinary `+`, `-`, `*` on them carry a proof obligation that the result doesn't overflow. Intentional or handled overflow uses explicitly named operations: `wrapping_add` (hashing, checksums), `checked_add -> Option`, `saturating_add`.
  - There is no implicit conversion between them. Narrowing conversions either require a proof that the value fits or return an `Option`.
  - Integer division (`/`) truncates toward zero, as in Rust. Its divisor must be nonzero; that's a proof obligation, like overflow.
  - Integer literals take their type from context, as in Rust: in `x + 1` with `x: Int8`, the `1` is an `Int8`, and a literal out of range for its type is a compile error. With no context, a literal is an `Int`. This is how literals get their type, not a conversion.

## 2. Type system

- **Algebraic data types:** records and variants (sum types). Named types are nominal; newtypes are cheap and encouraged.
- **Structural, extensible records** (as in PureScript), alongside nominal ones: `{ first: String, last: String | r }` accepts any record that has at least those fields. They use the same row-polymorphism machinery as effect rows (§3). Rule of thumb: domain types, and anything with an invariant, are nominal; structural records are for plumbing, such as options, configuration, and intermediate results.
- **Refinement types** (`Int where self >= 0`), with proof obligations discharged automatically by an SMT solver. This is the Liquid Haskell / F* approach: most of the value of dependent types, with proofs mostly automatic. The prelude names the most common one: `Nat` is `Int where self >= 0`.
- **Inference never guesses refinements.** Type inference picks base types for generic parameters. A refinement on a type argument comes only from what the code states:
  - an annotation or the expected type (`let total: Cents = fold(...)`);
  - an argument whose declared type is refined (`fold(items, initial: start, ...)` with `start: Cents`);
  - a declared type it's nested in (`write(ledger.checking, ...)` with `checking: TVar[Cents]` makes `write`'s `A` a `Cents`).

  In `fold(items, initial: 0, ...)` the accumulator is just an `Int`. Predictable beats clever.
- **A type variable's refinement travels with its instantiation, by parametricity, where nothing else can produce one.** If `fold`'s `B` is instantiated as `Cents`, then the `B` values going in (`initial`, and what `step` returns) must be `Cents`, and every `B` coming out (`step`'s accumulator parameter, the result) is one. It's what lets `fold` carry a refinement through a callback without Liquid Haskell's abstract refinements. But parametricity only says a function produces `B`s from the `B`s it's given, and with effects that's not all it's given. So the rule is:
  - The refinement may be *assumed* of an output only if every input of type `B` is checked. An input is checked if it's a parameter of type exactly `B`, or a function argument whose `B` results are checked (a lambda, whose body is). The callee must also have no other source of `B`: it must be a function with a body, not a primitive or an effect operation (except `atomically`, which is trusted to return its function's result), and none of its effects may mention `B`. Nor may `B`'s class constraints make one. `Num`'s `negate` and `from_int`, the arithmetic operators of `Add`, `Sub`, `Mul` and `Div`, and the literals of `IntLiteral` all make new `B`s from nothing checked. So a variable is unsafe if any of its classes, or their superclasses, has a method whose result mentions it, or has no methods written at all (its instances come from the runtime). Only the comparison classes (`PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`) are known to make nothing. A marker class isn't safe just because it has no methods: `FixedWidth` gives `Wrapping[I]` its arithmetic, and a `Wrapping` gives back an `I`, so `x xor x` makes a zero.
  - A `B` nested in an input (`Option[B]`, `List[B]`) isn't checked, so its presence rules the assumption out. So does a step function passed by name.
  - Otherwise the instantiation is ignored. Only the declared types count: `let n: Nat = unwrap_or(Some(-20), default: 0)` must prove `n >= 0` from `unwrap_or`'s own spec.
  - **A TVar's refined contents are always owed.** This is the other direction. When `A` is instantiated as the contents of a `TVar[Cents]` (`put(balance, -5)`, with `put[A](t: TVar[A], v: A)`), the callee may write any `A` it's handed into that TVar. So every `A` going in owes `Cents`, whether or not anything is assumed coming out: a parameter of type exactly `A`, or a function argument's `A` result. An `A` that could get in some other way is unprovable: inside another type (`List[A]`), as a callback's argument, through the result (a returned `(A) -> Unit`), as a resumed operation's result, or made inside the callee by a class constraint (`put_neg[A: Sub]` can write `v - v - v`). Such a function can't be used as a value either, since then nothing would check its inputs.
- **A function value is contravariant in its parameters.** One given where `(Cents) -> Int` is declared may need no more of its arguments than `Cents`: `needs_positive(y: Int where y > 0)` doesn't fit. Its results must have what the type promises. The verifier checks this where the value is given as an argument, a constructor field, a record update or an annotated `let`. A function with a precondition or a refined parameter can't be let out as a value any other way, since nothing would check it. "Refined" fails closed: a parameter is refined if the verifier would assume anything of it, including through an alias with arguments (`NonEmpty[Int]`). A fixed-width integer's range doesn't count, since every value of the type is in it.
- **Function-typed parameters can carry refinements that mention the other parameters.** That's how facts about a collection reach a callback. The standard `fold` is declared as
  ```
  function fold[A, B, E: Effects](
    xs: List[A],
    initial: B,
    step: (B, A where contains(xs, self)) -> B effects { E },
  ) -> B
  ```
  so inside `step` the element is known to come from `xs`. With `all(xs, p)` in scope, a standard lemma then gives `p(element)`. This covers the common case. Liquid Haskell's more general *abstract refinements* (generic types parameterized by a predicate) are deferred until a program needs them.
- **Explicit proofs** for obligations the solver can't discharge on its own. These are written as ordinary code (lemmas, assertions, `calc` blocks), not as tactics; see §4.1.
- **Higher-kinded types** for Functor/Traversable-style abstraction. With algebraic effects, the main historical driver of HKT-heavy code (monad transformer stacks) mostly disappears.
- **Typeclasses/traits with global coherence.** No orphan instances, so "which instance is used here?" always has exactly one answer. Alternative instances for the same type (e.g., a second ordering) go through newtypes, as in Haskell.
- **Typeclass laws are proof obligations.** A class declares its laws (e.g., `Eq`: reflexive, symmetric, transitive), and every instance must prove them. Derived instances get the proofs automatically, and the verifier can rely on the laws. A lawless instance, like Haskell's `Eq Double`, can't be written. An instance that uses `assume` to get past a law lands in the trust ledger.
- **No ML-style module system.** Modules are namespaces only, not values, and there are no functors (functions from modules to modules). Typeclasses cover the same ground in a form far more familiar to both developers and LLMs.
- **No implicit coercions or conversions.**
- **Invalid states unrepresentable** as a design norm for the standard library and idiomatic code.

### 2.1 Text and Unicode

The language's syntax is ASCII (§6), but the text it processes is fully Unicode. The design applies the type-driven principle to text: the unit of every text operation is explicit.

- **`String` is always valid UTF-8.** That is a type invariant: no operation can produce an ill-formed `String`.
- **`Bytes` is a separate type.** `decode_utf8(bytes)` is the only way across, and it fails with `Fail[DecodeError]` on ill-formed input (see §3 on the failure convention).
- **`Char` is a Unicode scalar value** (any code point except surrogates, as in Rust), so a lone surrogate cannot exist.
- **No unqualified length or integer indexing.** "Length" is ambiguous, and the ambiguity is a classic source of bugs, so there are explicit views instead. They are ordinary functions, since there's no method syntax (§6):
  - `bytes(s)` — UTF-8 code units: `byte_count(s)`
  - `chars(s)` — scalar values: `char_count(s)`
  - `graphemes(s)` — extended grapheme clusters (UAX #29), i.e. what a user sees as one character: `grapheme_count(s)`

  A reader always knows which unit is meant; there is no `length(s)` to misread.
- **Indices are opaque per view** (as Swift does it): an index into `chars(s)` is a different type from an index into `bytes(s)`. Slicing by byte offset requires a refinement proof that the offset falls on a character boundary (`where is_char_boundary(s, i)`), so splitting a multi-byte character is a compile-time error, not a runtime panic.
- **Equality compares scalar values exactly,** with no normalization. Unicode normalization is explicit (`normalize(s, form: NFC)`), and normalized text has its own refined type (`String where is_nfc(self)`), so "already normalized" can be required in a signature.
- **No ambient locale.** Locale-sensitive operations (case mapping, collation, formatting) take a `Locale` argument. The locale-independent versions say so in their names (e.g. `to_lowercase_invariant`). This is the same no-ambient-authority rule as for effects.
- **Platform strings are not `String`.** File paths, environment variables, and process arguments may not be valid Unicode on every platform, so they have their own types (`Path`, `OsString`, as in Rust), with fallible conversion to `String`.
- **Literals:** `"..."` with `\u{...}` escapes; raw strings for regexes and paths.
- **Interpolation goes through a trait,** so it's extensible: when the result is a `String`, `"Hello, ${name}"` formats `name` via its `Display` instance. Interpolation is also *target-typed* (like Swift's `ExpressibleByStringInterpolation`). When the literal's expected type is `Sql`, `Html`, or `ShellCommand`, that type's own interpolation instance handles each interpolated value, parameterizing or escaping it. Injection bugs become type errors: there is no way to build a `Sql` value by pasting raw strings together. The `${...}` syntax is provisional; it's the form most widely used across languages (JavaScript, Kotlin, Scala, shell).
- **The Unicode version is pinned per package version, and proofs never depend on it.**
  - Segmentation and normalization tables are compiled into the binary, not taken from the OS, so behavior is the same on every machine a build runs on.
  - Moving to a new Unicode version is a standard-library version bump, pinned by the lockfile.
  - In the verifier, version-dependent functions (`grapheme_count`, `normalize`) are opaque. They come only with facts that hold in every Unicode version (e.g., `grapheme_count(s) <= char_count(s)`), so a Unicode upgrade can never break a proof.
  - That fact library is deliberately conservative. It holds only facts that are trivially true or follow from Unicode's stability policies: `grapheme_count(s) <= char_count(s)`; the empty string has no graphemes; `grapheme_count(take_graphemes(s, count: n)) == n` when `n <= grapheme_count(s)`.
  - Grapheme counts of concatenations are **not** in it. Whether there's a break where two strings join depends on context (regional-indicator pairs, emoji joiner sequences), and those rules have changed between Unicode versions. Specs should be phrased in terms of `take_graphemes` and prefixes instead, as `examples/04_text.clk` does.

### 2.2 Equality, ordering, and floating point

This follows Rust's split between partial and total equality and ordering, but the laws are enforced by proofs rather than documentation (§2).

**The hierarchy:**
- `PartialEq`: `==` is symmetric and transitive, but not necessarily reflexive.
- `Eq` extends `PartialEq`: `==` is also reflexive (`x == x` for every `x`), making it an equivalence relation.
- `PartialOrd`: comparison may report that two values are unordered (`compare` returns `Option[Ordering]`).
- `Ord` extends `PartialOrd` and `Eq`: a total order.
- `Hash` requires `Eq`. Hash maps, sets, and `sort` require `Eq`/`Ord`.

**Equality is not identity.** A lawful `Eq` makes `==` an equivalence relation, but two values can be `==` and still be distinguishable. The verifier substitutes equals for equals (from `x == y`, conclude `f(x) == f(y)`) only where `==` really is identity:
- primitive types other than floats;
- spec-only theories like `Multiset`;
- types whose instances are derived, and whose fields' instances are all identity, recursively.

A derived `PartialEq` over a `Float64` field isn't identity, since `P(x: nan) != P(x: nan)`. A type variable `A: PartialEq` gets nothing beyond its class's laws. The same rule decides when `<=` is a total order, except that a type variable constrained by `Ord` gets totality from its class.

**Specs say identity with `identical(a, b)`.** It needs no instance and works on any type, so a postcondition on a generic `List[A]` can say `identical(append(front: result.prefix, back: result.rest), xs)` without demanding `A: PartialEq`. For a `Float64`, `identical(x, x)` holds while `x == x` doesn't, since NaN is never `==` to itself; the verifier knows the difference.

**Floats** (`Float32`, `Float64`) implement `PartialEq` and `PartialOrd` with IEEE 754 semantics (`NaN != NaN`; `-0.0 == 0.0`). They do not implement `Eq`, `Ord`, or `Hash`. Two standard wrappers give them the stronger instances:
- **`NonNan[F]`** is a newtype with the refinement `not is_nan(self)`. It has `Eq` and `Ord` with IEEE semantics. `-0.0 == 0.0` still holds, so by the rule above its `==` is not identity. You construct one with a proof, or through a function that returns an `Option`. Arithmetic on `NonNan` values returns plain floats, because NaN can reappear (`inf - inf`).
- **`Total[F]`** has `Eq`, `Ord`, and `Hash` via the IEEE 754 `totalOrder` relation (`-0.0 < 0.0`; NaNs are ordered by sign and payload), under which `==` is identity. Use it for map keys, sets, deduplication, and sorting.

`sort` on a `List[Float64]` doesn't typecheck; use `sort_by(xs, compare: total_order)` or convert to `NonNan`. Rust's common workaround, `partial_cmp(...).unwrap()`, which panics on NaN, has no equivalent here, because unwrapping an `Option` requires a proof that it holds a value.

**Operator traits are lawless; algebraic classes are lawful.** `+` and `*` come from operator traits (`Add`, `Mul`) that state no laws. Algebraic classes (`Semigroup`, `Monoid`, `Ring`) state their laws, such as associativity. Float addition isn't associative, so `Float64` implements `Add` but not `Monoid` or `Ring`; `Int` implements all of them.

**Generic numeric code: `Num`.** Code that is generic over integers and floats uses `Num`, which, like Haskell's `Num`, states no algebraic laws:

```
class Num[N] extends Add[N], Sub[N], Mul[N]
  function negate(x: N) -> N
  function abs(x: N) -> N
  function from_int(n: Int) -> N
end
```

- **Operator traits carry a domain predicate.** `Add`, `Sub`, and `Mul` each have a predicate saying when the operation is defined; by default it is always defined. That's how `+` on fixed-width integers gets its overflow obligation (§1). `Num` additionally requires every operation to be defined for all inputs, so generic code never has to discharge an obligation it can't see.
- **Instances:** `Int`, `Float32`, `Float64`, and `Wrapping[I]` for each fixed-width integer type `I`. `Wrapping[I]` does arithmetic modulo 2^n, so it is defined for all inputs. Plain fixed-width integers are not `Num`, because their arithmetic is partial. Code generic over widths uses a `FixedWidth` class of explicitly named operations (`checked_add`, `wrapping_add`, …).
- **Literals in generic code:** with `N: Num`, the `2` in `x * 2` means `from_int(2)` (see §1 on literal typing).
- **`Ring` extends `Num` and adds the laws,** just as `Eq` extends `PartialEq`. `Int` and `Wrapping[I]` are `Ring` (the integers modulo 2^n form a ring); floats are only `Num`. Code whose correctness depends on algebra asks for `Ring`; code that only needs arithmetic asks for `Num`.
- **Proofs over generic `Num` code are limited.** The verifier knows no laws for an arbitrary `N: Num`, so properties that need algebra, such as "rearranging a sum doesn't change it," can't be proven generically. Prove them for `Ring` or for specific types.
- **Regrouping operations requires the law.**
  - `sum[N: Num]` is defined as a sequential left fold, so its result is exactly specified even for floats.
  - Parallel `reduce` regroups operations, so it requires a lawful `Monoid` (such as `Sum[Int]`). That preserves §5's promise that parallelism is deterministic.
  - Floats get explicit alternatives: `float_sum` (compensated, or Kahan, summation), and a parallel float sum with a fixed tree shape. The parallel version is deterministic but may differ from the sequential sum.

**Verifying float code.** SMT solvers support a bit-precise theory of IEEE floats, but it's slow.
- By default, float operations are opaque to the verifier. Proofs work from a library of facts: comparisons agree with `total_order`, NaN propagates, the `sqrt` of a non-NaN value `>= 0` is not NaN, and so on.
- A lemma can explicitly opt into the bit-precise theory.
- In practice, most float specs are about NaN, finiteness, and ranges, not exact values.

## 3. Effects

- **Algebraic effects with row polymorphism** (Koka-style), with user-definable effects and handlers.
- **No ambient authority.** Code can perform only the effects in its signature; `main` receives the root capabilities.
- **Parameterized effects,** so authority is precise and visible in the signature:
  ```
  effects { Http[host: "orders.internal"], Fs[read: "/etc/app"], Clock, Log }
  ```
  A reviewer can answer "can this touch the network?" from the signature alone.
  - **What a parameter can be:** a literal (`"orders.internal"`), `any`, or the name of one of the function's own value parameters. `Fs[read: path]` means "reads only the file it was given." The last form covers resources chosen at runtime, such as files named on the command line, while keeping the signature specific.
  - **How parameters are checked:** an effect's parameters become preconditions on its operations. Under `Http[host: h]`, `get(url)` requires `url.host == h`; under `Fs[read: p]`, `read_bytes(q)` requires `q == p`. The verifier proves these like any other precondition.
  - **Subsumption:** code may call a function whose effect is no more permissive than its own. `Fs[read: any]` covers `Fs[read: path]` for every `path`; `Http[host: "a"]` covers only `Http[host: "a"]`.
  - Globs and path prefixes may come later (open question 2).
  - **Every parameter is written out.** `Fs` alone is an error, and `Fs[read: any]` must say so. A reviewer should never have to know a default to read a signature.
  - **An operation's precondition can name its effect's parameters.** `Http`'s `get` is declared `requires url.host == host`, where `host` is the parameter granted where `get` is performed. Under `any`, such a precondition is dropped.
  - **A function used as a value can't keep a parameter that names its own argument.** `read_bytes` has `Fs[read: path]`, but `map(paths, read_bytes)` reads whatever paths it's given later. As a value, its type widens to `Fs[read: any]`, so passing it needs that authority.
  - **The type checker checks `any` and differing literals; the verifier checks the rest.** At `read_bytes(p)` under `Fs[read: path]`, the verifier must prove `p == path`.
- **Effect polymorphism** for higher-order functions (`map` is as effectful as the function you pass it).
  - **Rows unify Koka-style, with scoped labels.** A row may hold the same effect twice (`{ Fail[E], Fail[F] }`), and the first one is what an operation reaches, which is the innermost handler. That's what `map_failure` needs, since inside it two `Fail`s are in play.
  - **A call's effects must be covered by those allowed where it's made.** A row variable (`map`'s `E`) takes whatever is allowed at the call, so a function passed to `map` may perform what the code around the call may.
  - **A declared function's row is closed, but used as a value it's open.** `insert_order` (`{ Db[database: "warehouse"] }`) can be passed where more effects are allowed.
  - **A handler adds its effects to the row of the code it handles,** with `any` for their parameters, since the handler decides what its operations mean. `resume` performs whatever is allowed outside the handler.
  - **A handler takes every operation of the effects it handles** (Koka's rule). A handler for `print_error` alone would grant `print_line` to code whose signature says it's pure, because an operation without a clause goes on outward.
  - **`resume` is one-shot, and only ever called.** A clause calls it at most once on any path, and never stores it or captures it in a function value. STM and in-place reuse both depend on that.
  - **`resume` owes what the operation promises:** its result type and its `ensures`, since the handled code assumes both after performing it. `old(...)` in the postcondition means the state where the operation was performed.
  - **A clause for a generic operation works at every type.** `gen[A]() -> A` is used at whatever `A` each call site wants, so in the clause `A` is rigid: `on gen() => resume("forty-two")` is a type error. Each call's `A` is its own, so no value of type `A` may outlive the call. Nothing made outside the clause may come to hold one: not the handler's result, and not a TVar made before the `handle`, which could carry one call's argument to the next call at another type. The checker enforces this with levels, as in OCaml and GHC: a type variable made outside the clause can't be bound to a type that mentions the clause's `A`.
  - **`Stm` can't be handled in user code.** Only `atomically` handles it. The verifier models `read` and `write` as the real heap and `retry` as rolling back; a user handler could drop a write or catch a `retry` and commit. Any future effect whose operations the verifier gives built-in meaning gets the same rule.
  - **A library hides the effects it uses internally.** With scoped labels, an operation reaches the innermost handler of its effect. So a library function that handles `Fail[E]` internally, say to exit a fold early, would also catch a callback's own `Fail[E]`, and no signature would show it. The rule: code that handles an effect only for its own purposes uses a private effect type (one not marked `public`, §6), never a public one like `Fail[E]`. No other module can name a private effect, so no callback can perform it and the library's handler can't catch one by accident. What's left unchecked is a library handling a public effect for its own purposes. `attempt` and `map_failure` handle their callback's `Fail` because that's their contract. Masking or lexically scoped handlers (Biernacki et al., POPL 2019) would make that checkable too (open question 9).
  - **`main` may perform only the root effects** the runtime provides: `Console`, `Args`, `Fs`, `Http`, `Db`, `Log`, `Atomic` and `Spawn`. Anything else must be handled inside it.
- **Built-in effects** include at least `Diverge`, `Fail[E]`, `Stm`, `Spawn`/concurrency, I/O families, and `Ffi`.
- **Failure convention.** Operations that can fail in the normal course of things (I/O, parsing, decoding) perform `Fail[E]`. Code then reads in direct style, and errors propagate without any `?`-style syntax. `Result` is for failure as *data*: values you store or collect, or return to a caller who will inspect them. Three standard functions convert between the two:
  - `attempt` turns a computation that performs `Fail` into a `Result`.
  - `or_fail` turns a `Result` into `Fail`.
  - `map_failure` converts one error type into another, adding context along the way.

## 4. Verification

- **Contracts:** `requires` (preconditions), `ensures` (postconditions), and type/data invariants.
- **`old(e)`** in a postcondition means the value of `e` when the function was entered. It only matters for code with state (`Stm`, §5).
- **Termination** is proved automatically. Structural recursion needs no annotation: a function calling only itself on a part of a parameter, taken apart by a pattern, and the same parameter at every call. Calls taking turns, shrinking one parameter while growing another, needn't terminate. (`ping(t, Cons(h, ys))` and `ping(Cons(h, Nil), t)` loop forever.) Anything else states a `decreases` measure: an integer, or a tuple of integers compared lexicographically (`decreases (length(tokens), 2)`), as mutually recursive functions often need. It must be an integer because the argument is "goes down and stays non-negative", which a real number can do forever.
- **Specs are well formed.** A call in a `requires` or `ensures` owes its callee's precondition, given the clauses before it, just as a call in code does. Otherwise `ensures at(xs, index: 5) == 0` would look meaningful on a short list and mean nothing. The same goes for refinements (in aliases, fields, parameters, results and `let` annotations, each given the refinements before it), invariants, and `decreases` measures. A function's definition unfolds, and its contract applies, only where it may be called: where its parameters' refinements and its precondition hold. Outside that, `f(x) == f(x) + 1` has no solution, and assuming it proves anything. The two rules back each other up: `type Fixed = Int where pos_id(self) == self`, with `pos_id(x: Int where x > 0)`, is ill formed, and even if it weren't, `pos_id(-3)` would be unconstrained, not positive.
- **What a function establishes stays with the code that ran.** Facts learned inside a function value's body, a handled computation, or a handler clause aren't known afterwards, since that code may never run or may be cut short.
- **Graded depth per module:** types only → refinements → full functional correctness, so proof effort goes where bugs are expensive.
- **What the solver reasons about:**
  - Automatic refinements use quantifier-free theories: integer arithmetic, ADTs, uninterpreted functions, and built-in collection theories.
  - **Nonlinear arithmetic is allowed.** `price * quantity >= 0` is ordinary business code, so it can't be ruled out. It's undecidable in general, so the checker helps the solver: for every product in an obligation, it adds sign facts as hypotheses (a product of non-negatives is non-negative, and so on). The fixed budget below still bounds each obligation.
  - **Built-in collection theories.** As in Dafny, `Set`, `Multiset`, `Seq`, and `Map` are known to the solver, and `List` has built-in abstraction functions (`multiset(xs)`, `elements(xs)`, `contains(xs, x)`). Specs like "is a permutation" (`multiset(result) == multiset(xs)`) then need no quantifiers. The theory includes the rule that `all(xs, p)` and `contains(xs, x)` together give `p(x)`. That's how a fact about a list reaches a callback over its elements (§2).
  - **Fixed-width values carry their range.** Every value of type `UInt8` is known to be in 0..255, so code reading bytes from a list needs no extra facts to call a function that takes a `UInt8`.
  - **Evaluation isn't search.** A definition unfolds one level automatically (§4.1), but a call whose arguments are all constructors, like `length(Cons(x, Nil))`, unfolds a few levels further, since that is evaluation, not search.
- **Solver predictability:**
  - Give each proof obligation a fixed solver budget (resource limit rather than wall-clock), so proofs don't break because of machine load or unrelated changes.
  - Failed obligations report a concrete counterexample.
- **Executable examples.** Examples in doc comments run as tests, to complement formal specs, which are easy to get subtly wrong.
  - An example is one line, `--| example: describe("naïve") == "naïve: 5 graphemes, ..."`. Or it's a block: an `--| example:` line followed by more-indented lines that end in an expression.
  - The expression must be a `Bool`. An example of the form `a == b` that fails reports both sides.
  - Examples are type-checked like any other code, and see exactly the names the module sees. A broken example is a compile error, not a silently skipped test.
  - Examples can't use built-in effects (no printing, no files). Effects an example handles itself, such as `attempt` or a `Trace` handler, are fine.

### 4.1 Proof style: proofs as code

When the solver can't discharge an obligation unaided, the author writes a proof. Proofs are written as **ordinary code in the language itself**, and the SMT solver fills in the gaps between the steps. Dafny and F* call this style *auto-active verification*. There is **no tactic language** in v1.

**What a proof needs to do.** Proofs are machine-checked, and they can neither weaken a spec nor change runtime behavior, so reviewers never need to read them. (The only exceptions are trust escapes, which are in the trust ledger; see §7.) So the requirements are:

1. LLMs can write them reliably.
2. When a proof fails, the error says what to fix, so the generate → check → fix loop converges.
3. They're separable, so review tooling can collapse them like function bodies.
4. They're stable, so they don't break after an unrelated change or a solver upgrade.

**Why not tactics.**

| | Tactics (Lean, Coq) | Raw proof terms | Proofs as code (Dafny, F*) |
|---|---|---|---|
| Readable without an editor | ✗ needs the live proof state | ✗ huge | ✓ each line states a fact |
| Separate language to learn | ✓ yes (bad) | partly | ✗ same language as programs |
| Robustness | brittle: scripts are search instructions | robust but expensive | good: hints are facts, not procedures |
| Power ceiling | highest | highest | lower, but enough for software |
| LLM familiarity | Lean (doesn't transfer to our language) | low | Dafny (fairly good; it's in LLM verification benchmarks) |

Two things decide it:

- **No second language.** Tactics are a separate language with their own semantics, and with no training data we can't afford two languages. A lemma is just a function whose postcondition is the theorem and whose body is the proof. Induction is recursion, and case splits are `match`.
- **Readable failures.** A failed tactic script reports on the tactic's internal state. A failed proof written as code reports something like "the assertion on line 14 isn't provable; here is a counterexample." An LLM can act on that, for example by adding assertions to narrow down which step fails.

What we give up is the hardest mathematics, which is beyond what an SMT solver plus hints can do. That's the right trade for a programming language. `proof` blocks are syntactically separate, so a tactic sublanguage could be added later without breaking anything.

**The constructs:**

- **`lemma`** declarations. A lemma is a function whose postcondition is the theorem, whose body is the proof, and which returns nothing.
- **`assert`** to state an intermediate fact. The solver must prove it, and can then use it.
- **Lemma calls**, which bring a lemma's postcondition into scope as a known fact.
- **`calc`** blocks: chains of equalities or inequalities in which each step names its justification (`by <lemma call>`, `by unfold f`).
- **`proof ... end`** blocks inside function bodies.
- **Induction** via recursive lemma calls, with termination checked through `decreases` like any other recursion.

**Soundness and stability rules:**

1. **Proof code is erased and checked as such.** Code inside `proof` blocks and lemmas can read program values, but program code can't read proof values. Proof code must be total and free of effects, and it is erased before code generation. Because it can never change what runs, it is safe for reviewers to skip. That's only true if the checks are complete, so they are:
   - A lemma can't have an `effects` clause, and a `proof` block, `assert`, or `calc` can't perform anything. In an `Stm` function, specs and proof code may `read` TVars, and nothing more.
   - Every recursive call terminates. That's proved by a `decreases` measure or, for a function calling only itself, by recursing on a part of a parameter that a pattern took apart. Without either, it's an error, not an assumption. In a mutually recursive group, every function needs a measure. A call in a `calc` justification counts. A group member used as a value inside its group is an error, because a call through a value can't be checked. So is a cycle through a class method: a call of a method runs whichever instance fits, in any module, so the checker gives it an edge to every instance's implementation across the program. A cycle through one is an error until termination through dispatch can be checked.
   - Anything the verifier can't check is reported as not proved, never as "ok". A proof is either checked or in the trust ledger.
2. **Verification is modular.** Across module boundaries, callers see a function's contract, and its body only when the body is part of its public surface: the function is public and its body names only public things (§6). That's what lets a spec use `length` or `all` from another module and unfold it. Any other body, such as one that reads a private field or calls a private helper, stays hidden, and so does the value of a constant defined that way. So a caller's proof depends only on what the module publishes, and a change to anything else can't break it. A change to a published body is an API change, like a change to a contract (§7.1).
3. **Definitions unfold one level automatically.** Where a function appears in a spec, the solver sees its definition expanded once and no further. Going deeper takes an explicit `unfold f`, and when a proof fails for lack of an unfolding, the error message suggests one. One level trades convenience for predictability, and the trade is cheap because adding an `unfold` costs an LLM nothing. This is the main defense against the solver searching unpredictably and timing out.
4. **Quantifiers are confined, and their triggers are explicit when ambiguous.** Quantifiers (`forall`, `exists`) are allowed only in explicit lemmas, not in automatic refinements. To use a fact like `forall x. P(x)`, the solver must decide which values of `x` to try. A *trigger* is a pattern such as `f(x)` that tells it: whenever a term `f(t)` shows up, try `x = t`. Bad triggers either make the solver try values endlessly (timeouts) or never fire (spurious failures). The compiler infers a trigger when there is one clear candidate, requires it to be written out when there isn't, and always shows inferred triggers in diagnostics. Quantifiers are the other main cause of SMT instability, as Dafny's history shows.
5. **The last resort is `assume`** (or a top-level `axiom`). Both always land in the trust ledger.

**Examples.**

A lemma, with induction written as a recursive call:

```
lemma reverse_preserves_length[A](xs: List[A])
  ensures length(reverse(xs)) == length(xs)
proof
  match xs
    case Nil => done
    case Cons(head, tail) =>
      -- induction hypothesis
      reverse_preserves_length(tail)
      append_length(front: reverse(tail), back: [head])
  end
end
```

A `calc` block, where every step names its justification:

```
calc
  length(reverse(Cons(h, t)))
    == length(append(front: reverse(t), back: [h])) by unfold reverse
    == length(reverse(t)) + 1 by append_length(front: reverse(t), back: [h])
    == length(t) + 1 by reverse_preserves_length(t)
    == length(Cons(h, t)) by unfold length
end
```

A proof inside a function body:

```
function merge_sort(xs: List[Int]) -> List[Int]
  ensures is_sorted(result) and multiset(result) == multiset(xs)
is
  ...
  let merged = merge(left: sort(a), right: sort(b))
  proof
    merge_preserves_sorted(left: sort(a), right: sort(b))
  end
  merged
end
```

### 4.2 Trusted base: what's verified vs. assumed

Anything the checker doesn't verify is assumed. The goal is to keep that set small and visible.

- **Runtime primitives** (machine arithmetic, `String` internals, the TVar runtime, the scheduler) are implemented in Rust or C and have assumed specs. They are the trusted computing base. One such assumption the verifier makes about a generic primitive: `atomically` returns its transaction's result, so a refinement on `A` passes through it (§2). Only the standard library declares primitives (`primitive type`, `primitive function`, `primitive instance`), since the runtime implements only its own. A program's own code reaches native code through FFI, which has its own place in the trust ledger.
- **The standard library is written in the language itself and verified**, wherever that's practical. Moving something from a primitive into the language is always a win.
- **FFI declarations have assumed specs** and appear in the trust ledger.
- **Assumed specs are checked at runtime in test and debug builds.** The compiler turns each assumed contract into a runtime check at the primitive or FFI call, and property-based tests generated from the contracts exercise them. A wrong assumption shows up as a failing test instead of a silently unsound proof.
- **The standard library publishes its own trust ledger,** like any package (§7.1).

## 5. Concurrency

**No async/await.** All code is written in direct style; there are no "colored" (async vs. sync) functions.

- **Green threads** (M:N scheduling, like Go, GHC, Java's virtual threads). Following OCaml 5, the scheduler can itself be implemented as an effect handler.
- **Structured concurrency.** Spawned tasks cannot outlive their enclosing scope. Cancellation is cooperative and happens at effect operations; no asynchronous exceptions.
- **STM for shared mutable state.**
  - `atomically` is the handler for `Stm`, and the only one (§3): it permits only the `Stm` effect, so irrevocable I/O inside a transaction is impossible by construction.
  - `retry` and `orElse` are operations of `Stm`. They're effect operations in form, but primitive in meaning: the verifier models them directly, which is why no other handler may take them.
  - Channels and queues are library code built on STM.
- **Deterministic parallelism for pure code** (e.g. parallel `map`) requires no effect, because purity makes it safe. Parallel reductions regroup operations, so they require a lawful `Monoid` (§2.2); otherwise results could vary from run to run, with float addition the classic case.

**STM makes concurrency verifiable.** Transactions are serializable, so each `atomically` block can be specified as a sequential state transition with ordinary contracts.
- Refinements on transactional variables (`TVar[Cents]`) are checked statically at every write.
  - **A TVar's refinement is part of its type.** Refinements are erased everywhere else, but not here: `TVar[Cents]` isn't `TVar[Int]`. If one could be passed as the other, a write through the `TVar[Int]` would break every `Cents` read through the other. (Function arguments are covered by contravariance, §2. A TVar is both read and written, so neither direction is safe.) So the refinement is named: `TVar[Int where self >= 0]` is an error, and the fix is `type Cents = ...` and `TVar[Cents]`.
  - **A TVar's contents can't hold a TVar,** directly or inside another value (§8). A function value counts as holding one, since it might capture one.
- **Multi-TVar invariants** can be declared and proved to be preserved by every transaction, statically. GHC tried checking such invariants at runtime and removed the feature; doing it statically is a potential differentiator.
  - **A type with an invariant owns its TVars.** Per-value invariants are only modular if no code can break a value's invariant without having that value in hand. TVars are shared freely, so that has to be arranged:
    - Only the type's own module can build a value, and every TVar field must be a new one (`new_tvar(...)` right there), so no two values share a TVar. So its constructor is only ever called directly: as a value (`let build = Cell`), it would build one around any TVar.
    - Nothing takes such a value apart with a pattern, and `with` can't copy one.
    - A TVar field is named only as what `read` or `write` acts on (`read(ledger.checking)`), so its TVar never escapes. Outside the module, it can only be read, and only if it's a public field (§6).
    - It owns only the TVars that are its direct fields, so those are all it may hold. A TVar inside another field (`Option[TVar[Int]]`, a record that holds one, a list, a function that might capture one) could be written by code that never names the owner. And the invariant reads only those fields: `read(x.f)`, with `x` its parameter.

    Together these mean only code that writes a value's TVars can break its invariant, and the write names the value (`write(x.f, ...)`). The verifier attributes the write from that syntax, not from the TVar's solver term, which may have simplified away from it (`p.left` of a `p` just built is the new TVar itself). This is the "ownership" discipline of Spec# and Dafny's `Valid()` idiom, applied to transactional state.
  - Form: `invariant name(x: T) <predicate> end`, where the predicate reads `x`'s TVar fields.
  - **What's checked.** A new value must satisfy the invariant. Code that writes a value's TVars must re-establish its invariant before returning (or committing), and it may break it in between (see `deposit` in `examples/07_ledger.clk`). Leaving abnormally counts as returning: before an operation other than `Stm`'s own (`fail`, any user effect), or a call that may perform one, the invariant must hold again, since a handler in the same transaction could catch it and commit. (`retry` is exempt, since it rolls the transaction back.) As a backstop, a value of an invariant type that an `Stm` function returns must satisfy the invariant. Every value it didn't write keeps its invariant, whatever it calls. So an `Stm` function may assume the invariant for its parameters, and a transaction may assume it for the values in scope.
  - Checking per function, rather than only at transaction boundaries, keeps the check modular: each function is verified on its own.
  - Inside specs, `read(tv)` means the TVar's value in the current transaction's view, and `old(read(tv))` means its value on function entry.
  - **A call to an `Stm` function must establish the invariant** for any argument this code might have broken, because the callee assumes it. Calling a helper while `deposit` has the invariant broken is an error, not a free assumption.
  - **A transaction must keep the invariant too.** A function value that may perform `Stm` where nothing else around it may, like the one passed to `atomically`, is a transaction wherever it's written. Any other function value runs at some unknown point, so it may assume nothing, and it must re-establish what it writes.
  - **Values of an invariant type nested inside other values are covered** by the same argument (a `List[Ledger]`, a record without an invariant that holds a `Ledger`). No code can break an invariant without writing `x.f` for some `x` of the type, so the write is tracked; and new values start out satisfying it. TVars nested inside the invariant type's own fields are a different matter, and are banned (above).
- **Aliasing is part of the spec.** The ledger's postcondition is false for a `Ledger` whose `checking` and `total` are the same TVar, and the verifier found that, with a counterexample that shows the two TVars are equal. Nothing in the record type ruled it out. The fix is in the type: each field is refined `where not identical(total, checking)`, and so on. TVars created by `new_tvar` are distinct, so `open_ledger` proves the refinements. Types that hold several TVars will usually want this.
- **No frame conditions, yet.** After a call to an `Stm` function, the caller knows only what the callee's postcondition says about TVars. A read-only helper must say `ensures read(x) == old(read(x))` for each TVar it leaves alone (open question 8). Ownership removes the worst of this for invariants: a transaction holding two values that calls a helper on one doesn't owe the other's invariant again.

**Known costs:**
- Long transactions can starve under contention.
- Reference counts must become atomic once data is shared across threads (see §8).
- TVars are the only way to create cycles in the heap (§8).
- STM can livelock (but not deadlock); channels can still deadlock logically.

## 6. Syntax

Optimized for reading. Concrete rules:

- **Explicit block delimiters** (`end`), not significant whitespace. LLM edit tools do string replacement, and indentation-sensitive code is a known way for those edits to fail silently.
- **Argument labels.** A call site must label:
  - every argument whose parameter shares its type with another parameter of the same function (ignoring refinements), as in `transfer(from: a, to: b, amount: x)`;
  - every `Bool` argument, so `f(true, false)` can't happen.

  Labels are always allowed. A label may be omitted (*punned*) when the argument is a variable of the same name, as in `append(front: tail, back)`. A declaration can give a parameter a separate external label: `function transfer(from source: Account, to target: Account, ...)`.

  **Labels confirm; they never reorder.** Arguments always appear in declaration order, so every call to a function reads the same way. A label that doesn't match the parameter in its position is an error.

  **`_` as the external label** declares a parameter positional-only, which is for operations where order carries no meaning: `function bit_xor[I](_ left: Wrapping[I], _ right: Wrapping[I])`. The opt-out is visible in the declaration, where a reviewer sees it, and it's on the review surface (§7), since nothing checks that the operation really is symmetric. `subtract(_ a: Int, _ b: Int)` would defeat the rule.

  **Two parameters whose types are type variables count as sharing a type,** because a call can make them the same. `pair_up[A, B](first: A, second: B)` needs labels.
- **Explicit imports; no glob imports.** An import lists the names it brings in (`import Bank.Ledger (Account, transfer)`), so every identifier's origin is visible in the file.
- **A clash is resolved by renaming an import, and only a clash.** Two things a module sees by one name are an error: two imports, or an import and the module's own declaration. The fix is `import Land.Plots (area as plot_area)`. A rename is allowed only where it resolves such a clash, so a name differs from its declaration only where it has to, and searching for a function's name finds its uses everywhere else. A rename keeps the name's case, and renaming a record type renames its constructor with it. The new name can't already mean something: not a prelude name (`Circle as Some` would make `Some(...)` build a `Shape`), not the name of something else imported in the file (`area as perimeter` would make a search for `perimeter` find a call of `area`), and not a name code gives its own meaning (`resume`, `result`, `self`, `any`, `main`). An entity is imported under one name at most. Messages call things what the file calls them. For the same reason, no module can declare its own `old`: in a contract, `old(x)` means x's value on entry. Qualified references (`Plots.area(...)`) were rejected: `Plots.area` would read exactly like a field access, and every reference stays a plain name resolved through the import list, which is what having no method syntax buys. The prelude isn't a clash: a module's own declarations and explicit imports take its names.
- **Private by default; `public` on what other modules may use.** Making something public changes a module's API, so it should show in the diff, and the marker sits on the declaration it describes, where an LLM editing that declaration sees it. An export list at the top of the file would need a second edit somewhere else. Go-style capitalization was rejected because types are already capitalized.
  - **Declarations:** `public` goes before `type`, `function`, `lemma`, `effect`, `constant`, `class`, and `primitive`. A public class's methods and a public effect's operations are public with it. Instances are global and can't be marked, since hiding one would break coherence. Neither can an invariant, which belongs to its type.
  - **Records:** each field is public or private (`public id: Int`). Outside its module, code can read a record's public fields, but it can build, match, or `with`-update the record only if every field is public. Otherwise updating a public `user_id` while copying a private `signature` would forge a token. A record with no public fields is opaque, so no `opaque` keyword is needed. Unlike in Rust, private fields aren't how a record protects a refinement on its values: the verifier checks refinements at every construction in every module. They're for invariants a refinement can't state (a token is valid because this module issued it) and for changing a representation without breaking anyone.
  - **Variants:** a public variant's constructors are all public. Clients match it exhaustively, and wildcard dispatch is forbidden, so a constructor they couldn't name would leave them unable to match at all. To hide a variant's constructors, wrap it in a record with a private field.
  - **Newtypes:** `newtype public Int` exposes the wrapped value (as Rust's `pub struct Id(pub i64)` does), and `newtype Int` keeps it private, so only the module builds or unwraps one. Aliases are always transparent.
  - **A public declaration's signature and contract name only public things:** its parameter, result, and field types, its effects and class constraints, its `requires` and `ensures`, and the refinements in all of them. Callers can't satisfy a precondition they can't read. So a contract can't name a private function, type (even as a lambda parameter's annotation), or field, and it can't build, match, or `with`-update a value whose type keeps fields private, since that names those fields. A public field's refinement may mention only public fields. A function's body, its `decreases` measure, and a constant's value are its own business. But a body that names only public things is part of the public surface for verification (§4), so other modules' proofs can see it.
  - **Derived instances show only what's public.** Instances are global, so a derived one works in every module. A derived `Display` writes a public type's private fields as `..` (`Account(id: 3, ..)`, and `Token(..)` for an opaque newtype). `deriving (Decode)` is an error on a public type with anything private, since decoding builds a value, which other modules can't do. A module that wants its opaque type decodable writes the instance itself, deciding what a decoded value may be. A derived `Eq`, `Ord`, or `Hash` still compares every field: comparing values reveals no field, and a type whose private parts mustn't affect equality writes its own.
  - **A class without methods can't be instantiated by hand.** Such a class (`Decode`, `IntLiteral`, `Add`, `Eq`, `Template`, ...) gets its meaning from the compiler and runtime, which work by a value's shape. So an instance is a claim the compiler has to make good on. `instance IntLiteral[Foo]` for a record would type `5` as a `Foo`, which then fails at run time. `instance Decode[Ticket]` in a client, or a blanket `instance[A] Decode[A]`, would decode, and so build, a `Ticket` that only its own module may build. Instances of these classes come only from `deriving`, where the class is derivable, or from the standard library's `primitive instance`s. Instances of classes with methods can be written anywhere, since their methods are checked code under the usual visibility rules. A newtype that should get literals or arithmetic (`newtype Cents = Int`) would get them by deriving them, once that's supported.
  - **Instances don't overlap.** They're global, so two instances of a class that could fit the same type would leave it unclear which one a use picks. That's an error, whether the instances are written, derived, or primitive.
  - **A module's doc examples see everything it sees,** private names included, since they document the module from the inside.
  - **Imports can't form a cycle through a module with anything that runs** (functions, lemmas, constants, instances). Termination is checked within a recursion group, and recursion groups are found within a module, so two modules importing each other could recurse into each other unchecked (`ping` calling `pong` calling `ping`). A cycle among modules of only types, classes, effects, and primitives is harmless, and the standard library's core modules form one.
- **No shadowing.**
- **No custom operators;** a small, fixed set of built-in operators.
- **No point-free style or operator sections.**
- **No catch-all patterns where a variant is being dispatched on.** Consider each position in a `match` (the scrutinee itself, or a field nested inside it) whose type is a variant type defined in the current package.
  - If any arm matches a constructor at that position, no arm may cover the position with `_` or a variable, either directly or through a catch-all at an enclosing position.
  - The remaining variants are listed explicitly, using or-patterns, with `as` to bind the value: `case Cons((Plus | Star | RightParen) as token, _) =>`.
  - Adding a variant then forces a compile error at every site that dispatches on it.
  - Binding a variant-typed value *without* dispatching on it is fine: `case Cons(token, _) =>` is allowed when no arm tests `token`'s constructor.
- **Pipelines.** `x |> f(a)` means `f(x, a)`, and `x |> f` means `f(x)`. This is the only way to chain calls left to right. There is no method-call syntax, so name resolution stays simple: `f` is an ordinary function in scope. `|>` binds more tightly than comparisons and less tightly than arithmetic.
- **Comments go on their own line.** There are no end-of-line comments, so every comment attaches to the item below it, and the formatter never has to guess.
- **Results can't be silently discarded.** In statement position, an expression must have type `Unit` (or `Never`); anything else needs `let _ = ...`. Libraries provide `Unit`-returning variants where discarding the result is normal (e.g., `run_concurrently`).
- **Mandatory type signatures on top-level and exported items.** Signatures are the spec. Types are inferred inside function bodies, where annotations are mostly noise.
- **One canonical formatter** (gofmt-style), with no configuration.
- **ASCII-only syntax.** Keywords, operators, and identifiers are ASCII; non-ASCII identifiers would invite look-alike-character attacks and make the names in a diff ambiguous. Source files are UTF-8, and **string literals, character literals, and comments may contain any Unicode.** One exception, aimed at "Trojan Source" attacks (CVE-2021-42574): bidirectional control characters and invisible characters (zero-width joiners, etc.) are rejected anywhere in raw source, including comments. In literals they must be written as escapes (`\u{202E}`), so what a reviewer sees is what the program contains.
- **Familiar surface:** Rust/Scala/ML-flavored syntax over Haskell-flavored semantics (typeclasses, ADTs, purity). A more Haskell-like surface was considered and rejected: LLMs and most developers know the Rust/Scala family far better.

### 6.1 Concrete syntax (provisional)

Settled while writing the example programs; the prototype parser implements this.

- **Comments:** `--` for line comments, `--|` for doc comments. Doc comments may contain `example:` blocks, which run as tests.
- **Declarations:** `type`, `function`, `lemma`, `effect`, `invariant`, `constant`, `class`, `instance`, and `primitive` (below). Any but `instance` and `invariant` may start with `public` (§6): `public function transfer(...)`, `public primitive type Int`.
- **Imports:** `import Std.List (List, map)`, with `name as other_name` for a rename (§6).
- **Modules and files:** module `Bank.Accounts` is the file `Bank/Accounts.clk`, under the program's root: the directory the entry file's module name starts from (`Bank/Accounts.clk` declaring `Bank.Accounts` has the root `.`). `Std.*` is always the standard library's, and no other file may declare a `Std` module. Verifying a program verifies all of its own modules, since each relies on the others' contracts.
- **Visibility in types:** `public id: Int` for a record field, `newtype public Int` for a newtype's wrapped value. A variant's constructors take no marker.
- **Primitive declarations** are implemented by the runtime and are part of the trusted base (§4.2), so they appear in the trust ledger: `primitive type Int`, `primitive function sqrt(value: Float64) -> Float64` (a signature with clauses and no body), `primitive instance Add[Int]`.
- **Type declarations:**
  - `type Account = record ... end`, `type Token = variant ... end`, `type AccountId = newtype Int`, `type Cents = Int where self >= 0`.
  - `deriving (Eq, Decode)` follows the type, after `end` for records and variants. Deriving a class also derives its superclasses (`Ord` brings `PartialOrd`, `Eq`, and `PartialEq`). The derivable classes are `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Display`, and `Decode`. Each field's type must already have the instance.
  - A refinement in a type alias refers to the value as `self`; a field or parameter refers to itself by name (`amount: Cents where amount > 0`).
- **Type expressions:**
  - Function types are written `(A, B) -> C effects { E }`. A function type with no `effects` clause is pure.
  - Structural records are written `{ value: A, traces: List[String] }`, and are open with `| r`.
- **Functions:** `function name[type params](params) -> Type`, then clauses in this fixed order: `effects`, `requires`, `ensures`, `decreases`. Then `is`, the body, and `end`. Lemmas use `proof` in place of `is`.
- **Type parameters:** `[A, B: Ord + Display, E: Effects]`. `E: Effects` declares an effect-row variable.
- **Blocks:**
  - Statements are separated by newlines, and the last expression is the block's value.
  - The statements are `let pattern [: Type] = expr`, `proof ... end`, `assert expr`, `unfold name`, `done`, and expressions.
  - Indentation is never significant.
- **Line continuation:** a newline ends a statement unless the expression is unfinished, either because it's inside brackets or because the next line starts with a binary operator. A call's `(` must be on the same line as the function.
- **Control flow:** `if c then ... else if ... else ... end`; an `if` with no `else` has type `Unit`. `match e case p [if guard] => ... end`.
- **Patterns:** constructors (positional or labeled fields), literals (including chars), tuples, `_` for fields, or-patterns `p | q`, as-patterns `p as name`, and guards.
- **Lambdas:** `function(x) => expr` for a single expression, `function(x) is ... end` for a block. The same keywords introduce named and anonymous functions: a name after `function` makes a declaration, and `(` makes a lambda; `is` opens either one's block body. A lambda has no type parameters and no return type (annotate its parameters, or the binding it's assigned to), and a named function can only be declared at the top level. An earlier draft used `fn` for lambdas, but that made it the only abbreviated keyword, and having two keywords for one concept gave LLMs two ways to get it wrong: Rust habits write `fn name(` for a declaration, and JavaScript habits write `function(x)` for a lambda. Terseness is a writing convenience, and Clanker optimizes for reading. For the same reason a lambda's block body uses `is`, as a declaration's does, rather than its own `do`. `fn` and `do` stay reserved, so the near misses those habits produce get an error naming the right form rather than a bare parse error.
- **Handlers:** `handle expr on op(args) => ... on return(value) => ... end`. Inside a clause, `resume(value)` continues the computation. Resumption is one-shot.
- **Records:**
  - Construction: `Account(id: ..., balance: ...)`.
  - Update: `account with balance = 300, id = ...`.
  - Structural literals: `{ value, traces: [] }`, with punning.
- **Literals:**
  - Integers (`1_000`, `0xff`) and floats (`1.5`).
  - Chars (`'a'`, `'\u{1F600}'`).
  - Strings with `${...}` interpolation and `\u{...}` escapes.
  - Multi-line `"""..."""` strings with the common indentation removed, as in Swift and Java text blocks.
- **Top-level constants:** `constant name: Type = expr`.
- **Evaluation order:** left to right, including arguments, which matters because arguments can perform effects.
- **Prelude:** a small fixed set is in scope without imports:
  - the types `Bool`, `Int`, `Nat`, `String`, `Char`, `Unit`, `Never`, `List`, `Option`, `Result`, and their constructors;
  - the core classes `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Num`, `Display`.

  Everything else is imported explicitly. Each prelude name has a home module where it is defined: `String` in `Std.Text`, `Char` in `Std.Char`, `List` in `Std.List`, and so on. Importing a prelude name explicitly from its home module is allowed, though redundant.
- **A module's own declarations take precedence over the prelude.** A module can define its own `List` (as `examples/02_lists.clk` does). List literals like `[1, 2]` always build `Std.List`'s type, so such a module writes `Cons(1, Nil)`.
- **Reserved names in specs:** `result` (in `ensures` and return-type refinements) and `self` (in refinements). Because shadowing is an error, a parameter named `result` can't have an `ensures` clause that mentions it.
- **Canonical layout** (what the formatter produces):
  - Indentation is always two spaces per level. Nothing is aligned to a column, so renaming one thing never reindents its neighbours; alignment makes diffs noisy, and diffs are what reviewers read.
  - Lines are at most 100 columns wherever a break is possible.
  - Breaks go only where the parser accepts them: inside brackets, before a binary operator, and between statements.
  - `if`, `match`, `handle`, and block lambdas always span several lines.
  - A call whose last argument is a block lambda, list, record, call, or multi-line string "hugs" it: `fold(xs, initial: 0, step: function(sum, x) is` ... `end)`.
  - Clauses appear in the fixed order `effects`, `requires`, `ensures`, `decreases`.
  - In literals, visible characters are written as themselves, and invisible ones (formatting controls, non-ASCII spaces, control characters) as `\u{...}` escapes.

## 7. Review tooling

These tools are first-class parts of the language, not afterthoughts:

- **Review-surface diffs.** Changes are classified as spec, effect-signature, implementation, or trust-escape, e.g. "412 implementation lines changed, 0 spec lines changed, verifier passed."
- **Spec-weakening alarm.** The main way an LLM can cheat is to weaken a spec until the proof goes through, so every weakened postcondition, strengthened precondition, or widened effect row is flagged. Lints catch vacuous specs (`ensures true`, preconditions that can never be satisfied).
- **Trust ledger.** Every `assume`, `axiom`, FFI declaration, and `unsafe` is enumerated per change. Together with spec changes, this list is the complete set of things a human must look at.
- **Signals that change what a spec means.** Positional-only parameters (`_` labels, §6) are listed, since nothing checks that order doesn't matter. So are postconditions of functions that can fail or never return. `ensures result > 0` means "if it returns", and a function that always fails satisfies every postcondition. A lint flags a function that can't return normally at all.
- **Structured diagnostics.** Errors come out as machine-readable JSON with suggested fixes, and failed proofs come with counterexamples. The generate → check → fix loop is the core workflow, and the compiler's output is designed for it.

### 7.1 Packages and versioning

- **Semantic versioning is computed, not declared.** Elm does this for type signatures; Clanker extends it to contracts and effects. The tooling compares a package's public API against its previous release. That's everything marked `public` (§6), with its contracts and public fields, plus the bodies other modules' proofs can see (§4):
  - *Compatible (minor):* adding items; weakening a precondition; strengthening a postcondition or a return-type refinement; narrowing an effect row.
  - *Breaking (major):* any other change to a public signature, contract, or effect row, such as strengthening a precondition, weakening a postcondition, or widening an effect row.
- **Dependency upgrades are reviewed as spec diffs.** Upgrading a dependency shows the contract and effect changes to the APIs you actually use, not its source diff.
- **Trust is transitive.** A package's trust ledger includes its dependencies' ledgers, so adding a dependency that uses `assume` or FFI shows up in review.
- **Lockfiles pin exact versions by content hash.**

## 8. Runtime model

The backend is deferred, but the runtime model leaks into the language's semantics, so it is decided early.

- **Reference counting with reuse** (Perceus / Lean 4's "Counting Immutable Beans"). Functional updates mutate in place when the value is uniquely referenced.
- **Thread-shared objects** are marked when they cross a thread boundary, and only those use atomic reference counts (Lean's approach).
- **Cycles are ruled out statically, for now.** Immutable, eager data cannot form cycles; TVars are the only way to make one.
  - A TVar's contents may not contain another TVar, directly or transitively. This is enforced by an automatically derived marker trait (like Rust's `Send`), so cycles are impossible and plain reference counting suffices.
  - The cost: users can't write fine-grained concurrent data structures, where each node is its own TVar. The standard library provides the important ones (concurrent map, queue) as trusted primitives (§4.2).
  - If real programs need more, add a backup cycle collector for TVar-reachable data and lift the restriction.
- **Monomorphization** of generics, including higher-kinded polymorphism. Polymorphic recursion is banned or boxed.
- **FFI** to C (and through it to platform GUI toolkits, etc.). Every foreign declaration carries an effect signature and an assumed spec, and appears in the trust ledger.
- **GUI model:** the Elm architecture (pure model, update, and view functions, with effects at the edges). Native widgets come in via FFI behind that interface.

## 9. Implementation

- **Compiler written in Rust.**
- **salsa** for query-based incremental compilation. A language server (LSP) and fast re-checking are needed from day one.
- **ariadne / miette** for human-facing diagnostics, plus JSON output for agents.
- **SMT via SMT-LIB over a subprocess,** so the compiler is solver-agnostic (Z3, cvc5) and can set a resource limit per obligation.
- **Arena-allocated syntax trees with index IDs,** to avoid ownership friction with tree-shaped data.
- **A reference interpreter over the core IR** as the first execution target. It lets doc examples run and STM semantics be tested before native codegen exists.
- **Native backend:** deferred. Candidates are Cranelift, LLVM, and C (as Lean does).

## 10. Prior art

| Language | What to take from it |
|---|---|
| **Lean 4** | Closest semantic match: pure, strict, dependent types, HKTs, compiled, RC with reuse. Differs on readability (tactic proofs, Unicode, notation, coercions), coarse monadic effects, and limited automation by default. |
| **Koka** | Algebraic effects with row types; Perceus reference counting; `div` as an effect. |
| **F\*** | Refinement types plus SMT, effects, proofs; extraction to native code. |
| **Liquid Haskell** | Refinement types as an add-on to an existing language; decidable refinement logic. |
| **Dafny** | Contract-based verification that working programmers can use; good failure reporting. |
| **OCaml 5 / Eio** | Effect handlers implementing direct-style concurrency with no async/await. |
| **GHC STM** | The STM design; the history of its (removed) runtime invariants. |
| **Elm** | The GUI architecture; compiler error messages as a product feature; semantic versioning enforced by the package tool. |
| **PureScript** | Row-polymorphic extensible records. |
| **Swift** | The string model (grapheme-based characters, opaque indices); target-typed string interpolation. |
| **Unison** | Content-addressed code (possibly relevant to review diffs). |
| **Rust** | Coherence rules, monomorphization, the `PartialEq`/`Eq` and `PartialOrd`/`Ord` split, the tooling bar. |
| **Go** | A single canonical formatter; green threads. |

## 11. Open questions

1. **Training corpus.** The surface is settled (§6). Still open: should we generate a large corpus of idiomatic Clanker early (e.g., by translating existing programs) for few-shot prompting or fine-tuning? And how do we keep it idiomatic as the language changes?
2. **How far effect parameters go.** Literals, `any`, and names of parameters are decided (§3). Still open:
   - **Globs, path prefixes, and values derived from configuration.** Prefix authority can't be enforced on strings alone: `"/etc/app/../shadow"` and a symlink inside `/etc/app` both escape. As in capability systems (WASI preopens, Capsicum), it needs resolution relative to a handle, enforced at runtime by the primitive and recorded in the trusted base. The verifier can't do it alone.
   - **Precise authority for function values.** Today `read_bytes` used as a value widens to `Fs[read: any]`, so every higher-order use of a precisely authorized function needs `any`, and authors will learn to write `any`. Function types could bind their argument (`(p: Path) -> Bytes effects { Fs[read: p] }`), and parameters could be sets (`Fs[read: in paths]`), so that `map(paths, read_bytes)` keeps a precise signature.
   - **Where each check lives.** Value parameters make types dependent. Today the checker compares them by spelling and the verifier compares them at calls. A cleaner split: the checker handles labels only, and the verifier handles every value parameter wherever one row becomes another.
3. **Interpolation details.** The `${...}` syntax is provisional (§2.1). Should interpolated expressions be restricted to simple forms (names, field access, calls) for readability?
4. **Native backend.** Deferred: Cranelift, LLVM, or emitting C.
5. **Is nonlinear arithmetic tractable in practice?** Sign facts plus a fixed solver budget (§4) is a bet. So far it holds: the prototype proves `price * quantity` and `total * 10 + digit` with no hints. That's only two programs.
6. **Abstract refinements.** Deferred (§2). Parametric instantiation (§2) covered the case that motivated them, a refinement flowing through `fold`. Revisit when a program needs a generic type parameterized by a predicate.
7. **Name.** "Clanker" is the code name.
8. **Frame conditions for `Stm` functions.** Today a callee's postcondition must list every TVar it leaves unchanged (§5). Ownership makes invariants modular without frames, but a postcondition about one TVar still doesn't survive a call that writes another. A `reads`/`writes` clause on the effect (`Stm[writes: ledger.checking]`) would fit the effect-parameter design and be visible in the signature. It's the dynamic frames approach (Kassios; Dafny's `reads`/`modifies`). Alternatively, frames could be inferred from the body, but that breaks modularity at primitives and function values. This needs larger STM programs to decide.
9. **Effect encapsulation.** A library's internal use of an effect can catch a callback's operations of the same effect (§3). For now, the convention is private effect types. The open question is whether to add masking (Koka's `mask`) or lexically scoped handlers, which would make it a checked rule.

---

## Appendix: examples

Worked examples of every feature live in [`examples/`](examples/). They are written in the syntax of §6.1, and they double as the prototype's test suite.
