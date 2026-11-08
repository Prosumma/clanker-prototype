# Open items

This is the single list of what's open in Clanker, and it's definitive. [`DESIGN.md`](DESIGN.md) records what's decided and why, and the [`README`](README.md) describes what the prototype does. Both point here for what isn't finished. Where either of them disagrees with this file, this file is right and the other one gets fixed.

An item leaves this file in the commit that resolves it, and its ID is never reused. Items that came out of an adversarial review say which finding they came from ("review #81").

There are four kinds:

- **Undecided:** a design question that needs a decision.
- **Deferred:** decided against for now, with what would make us revisit it.
- **Unbuilt:** decided, but not yet built in the prototype.
- **Limitation:** where the prototype misses true things or approximates. None of these lets it accept something false. Trusted assumptions are listed too, since they're where it could.

## Undecided

### O-1: Training corpus

The surface is settled (DESIGN §6). Should we generate a large corpus of idiomatic Clanker early, for example by translating existing programs, for few-shot prompting or fine-tuning? And how do we keep it idiomatic as the language changes?

### O-2: Effect parameters for globs, path prefixes, and configuration

Literals, `any`, and parameter names are decided (DESIGN §3). Prefix authority can't be enforced on strings alone: `"/etc/app/../shadow"` and a symlink inside `/etc/app` both escape. As in capability systems (WASI preopens, Capsicum), it needs resolution relative to a handle, enforced at runtime by the primitive and recorded in the trusted base. The verifier can't do it alone. (Review #42.)

### O-3: Precise authority for function values

`read_bytes` used as a value widens to `Fs[read: any]` (DESIGN §3), so every higher-order use of a precisely authorized function needs `any`, and authors will learn to write `any`. Function types could bind their argument (`(p: Path) -> Bytes effects { Fs[read: p] }`), and parameters could be sets (`Fs[read: in paths]`), so that `map(paths, read_bytes)` keeps a precise signature.

### O-4: Where each check on effect parameters lives

Value parameters make types dependent. Today the checker compares them by spelling when two function types are unified, and the verifier compares them at calls. A cleaner split: the checker handles labels only, and the verifier handles every value parameter wherever one row becomes another. (Review #35.)

### O-5: Interpolation details

The `${...}` syntax is provisional (DESIGN §2.1). Should interpolated expressions be restricted to simple forms (names, field access, calls) for readability?

### O-6: Native backend

Cranelift, LLVM, or emitting C, as Lean does (DESIGN §9). The runtime model (DESIGN §8) is decided independently of this.

### O-7: Is nonlinear arithmetic tractable in practice?

Sign facts plus a fixed solver budget (DESIGN §4) is a bet. So far it holds: the prototype proves `price * quantity` and `total * 10 + digit` with no hints. That's only two programs.

### O-8: Name

"Clanker" is the code name.

### O-9: Frame conditions for TVars

After a call to an `Stm` function, the caller knows only what the callee's postcondition says about TVars (DESIGN §5). A read-only helper must say `ensures read(x) == old(read(x))` for each TVar it leaves alone, and it can do that only for TVars it can name. Ownership makes invariants modular without frames, but a postcondition about one TVar still doesn't survive a call that writes another. Inside an invariant type's module, a function holding two values that calls a helper on one must re-establish the other's invariant if it wrote it.

Candidates: a `reads`/`writes` clause on the effect (`Stm[writes: ledger.checking]`), which fits the effect-parameter design and is visible in the signature (dynamic frames: Kassios, Dafny's `reads`/`modifies`); or frames inferred from bodies, which breaks modularity at primitives and function values. This needs larger STM programs to decide. Local state has frames already (DESIGN §3), since its regions name what a call can touch.

### O-10: Effect encapsulation

A library's internal use of an effect can catch a callback's operations of the same effect (DESIGN §3). For now, the convention is private effect types, which no other module can name. Should masking (Koka's `mask`) or lexically scoped handlers (Biernacki et al., POPL 2019) make this a checked rule, covering a library that handles a public effect like `Fail[E]` for its own purposes?

## Deferred

### O-11: Abstract refinements

Generic types parameterized by a predicate, as in Liquid Haskell (DESIGN §2). Parametric instantiation covered the case that motivated them, a refinement flowing through `fold`.

**Revisit** when a program needs a generic type parameterized by a predicate.

### O-12: Local named functions

A worker is a private top-level function (DESIGN §6). A `where` function that captures its wrapper's parameters would inherit their refinements silently, so its specification would depend on context its signature doesn't show.

**Revisit** if LLM-written code shows workers carrying many unchanged parameters. If it does, start with a `where` that scopes a helper without capturing.

### O-13: A cycle collector for TVars

TVars can't hold TVars, so data reachable through them can't form a cycle, and plain reference counting suffices (DESIGN §8). The cost is that users can't write fine-grained concurrent data structures where each node is its own TVar. The standard library provides the important ones as trusted primitives.

**Revisit** if real programs need such structures. Then add a backup cycle collector for TVar-reachable data and lift the restriction.

## Unbuilt

### O-14: Instances checked against their class

Instance members are verified, but nothing checks them against their class's method signatures. Until something does, three restrictions hold (review #8, #18, #70):
- class methods can't have `requires` or `ensures`, since every call would assume them;
- class method signatures' refinements aren't checked for well-formedness;
- recursion through a class method (a generic function calling a method whose instance calls it back) is rejected, since its termination isn't checked ([O-15](#o-15-termination-through-dispatch)).

When this is built, members must be matched to methods by the method's declared name. Today a member named after a renamed method's local name (`g_size` for `size as g_size`) is accepted, and the dispatch-cycle check doesn't see it (review round 13).

### O-15: Termination through dispatch

A call of a class method runs whichever instance fits, so recursion through one (a hand-written `Display[Tree]` that displays its children) is rejected today (DESIGN §4). Derived instances cover the common case. Checking it needs a measure that applies across dispatch.

### O-17: Instance dispatch at runtime

Instance members with bodies aren't dispatched by the interpreter. Class methods work for the built-in instances, by the shape of the value.

### O-18: Constraints on a type's parameters at use sites

`Wrapping[I: FixedWidth]` declares a constraint that isn't checked where the type is used.

### O-19: Open structural records

`{ value: A | r }` is in DESIGN §2, and the prototype doesn't support the `| r`.

### O-20: Literals and arithmetic for numeric newtypes

A newtype that should get literals or arithmetic (`newtype Cents = Int`) would get them by deriving them (DESIGN §6). Hand-written instances of those classes are rejected, since the compiler gives them their meaning. Deriving them isn't supported yet.

### O-21: Review tooling

DESIGN §7: the review surface, the trust ledger, and the spec-weakening alarm. That includes putting the postconditions of functions that perform `Fail` or `Never` on the review surface, since they hold only on normal return, with a lint (review #41).

### O-22: Packages and computed versioning

DESIGN §7.1: semantic versioning computed from public APIs (contracts, effects, and the bodies other modules can see), spec diffs for dependency upgrades, transitive trust, and lockfiles.

### O-23: Primitives the interpreter lacks

`decode_json` (it needs the target type at runtime), and the `Http` and `Db` effects. `10_order_sync.clk` type-checks but can't run.

### O-24: Grapheme segmentation

Segmentation is approximate for combining marks, ZWJ sequences, emoji modifiers, variation selectors, and regional-indicator pairs. Full UAX #29 isn't implemented.

### O-25: Verified doc examples

Doc examples are run (`clanker test`) but not verified.

### O-38: `assume` and `axiom`

The last resort for a proof (DESIGN §4.1, step 5), which always lands in the trust ledger (DESIGN §7). Neither exists in the prototype, so today there's no escape: a proof is checked, or it's reported not proved. (Review #87.)

### O-39: `unsafe` and FFI

Foreign declarations with an effect signature and an assumed spec, and `unsafe`, both in the trust ledger (DESIGN §4.2, §7, §9). Neither exists in the prototype. Assumed specs are also meant to be checked at runtime in test and debug builds (DESIGN §4.2). (Review #87.)

### O-40: Class laws as proof obligations

A class declares its laws, and every instance must prove them, with derived instances proving them automatically. The verifier may then rely on the laws (DESIGN §2). That includes the lawful algebraic classes (`Semigroup`, `Monoid`, `Ring`), and the lawful `Monoid` that a parallel `reduce` requires (DESIGN §2.2, §5). None of it is built: no class declares laws, and the only law the verifier uses is `Ord` totality, which is trusted ([O-34](#o-34-trusted-ord-totality)). (Review #87.)

## Limitations

### O-26: Refinements are erased in the checker

Except inside `TVar`, `Cents` is `Int` to the checker. The verifier proves refinements.

### O-27: Refinements inside a parameter's type arguments

`amounts: List[Cents]` doesn't make the elements `Cents` to the verifier. So they aren't owed either, and nothing relies on them. (Review #23.)

### O-28: Row unification uses scoped labels for `Local` too

When two function types are unified, `{ Local[Ra], Local[Rb] }` doesn't unify with `{ Local[Rb], Local[Ra] }`. Only `performs` matches `Local` by region.

### O-29: Distinctness of new TVars and cells

A new TVar or cell is known to be distinct from the others made in the function and from those in scope (parameters and locals), but not from ones reachable only through a value's fields. A cell parameter is known not to be a TVar parameter. Two cell parameters of different regions aren't known to differ, rightly: a caller can pass one cell as both.

### O-30: State through an effect-polymorphic callback

After `for_each(xs, action: function(x) => put(sum, get(sum) + x))`, nothing is known about `sum`, as after any call whose effects are a row variable. Folds keep what's known.

### O-31: A `handle` expression's value is unknown

Even for `handle 5 on ...`.

### O-32: Structural termination is narrow

It covers a function calling only itself, on one parameter. Mutual recursion, and recursion that shrinks different parameters by turns (`merge`), need measures.

### O-33: Floats and strings are uninterpreted

Facts about them come only from specs.

### O-34: Trusted: `Ord` totality

Class laws aren't checked ([O-40](#o-40-class-laws-as-proof-obligations)), and aren't used except for one: a type variable's `<=` is assumed total under `Ord`. For a hand-written `Ord` instance, that rests on a law nothing proves, so it belongs in the trust ledger ([O-21](#o-21-review-tooling)). It can't go wrong at runtime yet, since instance members aren't dispatched ([O-17](#o-17-instance-dispatch-at-runtime)). (Review #52.)

### O-35: Trusted: `atomically` returns its transaction's result

So a refinement passes through it (`let r: Cents = atomically(function() => read(b))`). DESIGN §4.2 records the assumption.

### O-36: Messages can show internal names

A type mismatch can show a clause skolem's internal name (`A of gen #0`, `E of go #0`) rather than the operation's own (review round 16).

### O-37: A call with effects forgets state

A call to a function that performs any effect other than `Stm` forgets every TVar and cell, apart from what its postcondition says. A handler around the call could take one of its operations and write state in the clause while the call runs, so a `Console`-only helper is no exception. The one exception is a call whose effects are only `Local[...]`, with each region's cell known, which forgets just those cells (DESIGN §3).
