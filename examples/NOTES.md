# Example programs: what writing them taught us

These ten programs were first written from `DESIGN.md` alone, before any compiler existed. They test whether an LLM can write the language from the design doc, and they surface the places where the design was vague or didn't work. They are the prototype's test suite. The `example:` lines in doc comments are the expected results.

| File | Exercises |
|---|---|
| `01_transfer.clk` | records, variants, refinements, newtypes, contracts, record update |
| `02_lists.clk` | generics, structural recursion, effect polymorphism, labels, lemmas |
| `03_numbers.clk` | floats, `NonNan`, generic `Num`, `Wrapping`, literal typing, indexing, pipelines |
| `04_text.clk` | Unicode literals, length units, graphemes, locales, interpolation |
| `05_wordcount.clk` | CLI `main`, root effects, `Fs[read: path]`, `Fail` and `map_failure` |
| `06_trace.clk` | user-defined effect, two handlers, structural records, block lambdas |
| `07_ledger.clk` | STM, a multi-TVar invariant, `old(...)`, structured concurrency |
| `08_calculator.clk` | lexer and parser, char patterns, lexicographic termination, or-patterns |
| `09_sorting.clk` | verified insertion sort, refined type alias, multisets |
| `10_order_sync.clk` | parameterized effects, SQL interpolation, refinement-checking decoders |

The syntax the examples settled on is now recorded in DESIGN §6.1.

## Findings and their resolutions

The first draft of the examples marked each problem with `-- FRICTION:`. All twelve are now resolved in DESIGN.md, and the examples have been updated to match.

| # | Finding | Resolution | Where |
|---|---|---|---|
| 1 | Nonlinear arithmetic (`price * quantity`) appears in the most ordinary code, outside the linear fragment. | Allowed. The checker adds sign facts for every product; the fixed budget still applies. Whether that's enough is now open question 5. | §4 |
| 2 | Facts about a list (`all(digits, is_ascii_digit)`) didn't reach a `fold` callback. | Function-typed parameters can refine their parameters using the enclosing function's other parameters; `fold`'s `step` gets `A where contains(xs, self)`. Abstract refinements deferred. | §2 |
| 3 | Effect parameters: what can they say, and how are they checked? A CLI could only say `Fs[read: any]`. | Parameters are literals, `any`, or names of value parameters (`Fs[read: path]`). They become preconditions on the effect's operations, with subsumption (`any` covers everything). | §3 |
| 4 | Should `fold(items, initial: 0, ...)` infer `Int` or `Cents`? | Inference never guesses refinements; they come from annotations and expected types. | §2 |
| 5 | The wildcard ban had loopholes (nested `_`, catch-all variables). | Defined per pattern position: once any arm dispatches on a local variant at a position, no arm may catch it all there. Use or-patterns and `as`. | §6 |
| 6 | Two error styles (`Result` and `Fail`) with no convention. | Operations that can fail perform `Fail[E]`; `Result` is failure as data. `attempt`, `or_fail`, and `map_failure` convert. | §3 |
| 7 | `truncate`'s natural spec needed grapheme counts of concatenations. | Not a version-independent fact, so not available. Specs use `take_graphemes` and prefixes instead. | §2.1 |
| 8 | "Is a permutation" needed quantifiers. | Built-in `Set`, `Multiset`, `Seq`, and `Map` theories, plus `multiset(xs)` and friends. | §4 |
| 9 | The label rule wasn't crisp, and DESIGN's own examples broke it. | Labels are required for parameters that share a type, and for every `Bool`. Punning is allowed. DESIGN's examples are fixed. | §6 |
| 10 | Nested calls read inside-out. | `x \|> f(a)` means `f(x, a)`. No method syntax, so name resolution stays simple. | §6 |
| 11 | `let _ = concurrently(...)` was noise. | The rule stays strict; libraries provide `Unit`-returning variants (`run_concurrently`). | §6 |
| 12 | Smaller points: two lambda forms, `deriving` boilerplate, escape-only emoji sequences, undefined TVar invariant semantics. | Both lambda forms stay. `deriving` stays explicit, because `Eq` is part of a type's reviewable surface. The ZWJ rule stays. Invariants are assumed on entry and re-established on exit of every `Stm` function. | §5, §6.1 |

## Costs we accepted

- **Or-patterns are verbose.** `08_calculator.clk` lists Token variants several times. That's the price of "adding a variant breaks every site that dispatches on it," and it's paid in exactly the places where a forgotten variant would be a bug.
- **No end-of-line comments.** Several first-draft comments had to move onto their own lines. That's slightly less compact, but every comment now attaches unambiguously to the item below it.

## What the type checker found

Getting the examples and the standard library through the checker (prototype step 2) turned up these, all now resolved:

- **No method syntax means no `s.chars`.** DESIGN §2.1 wrote string views as fields. They're now functions (`chars(s)`), and `08_calculator.clk` reads `text |> chars |> lex |> parse_expr`.
- **List literals versus a local `List`.** `02_lists.clk` defines its own `List`, but `[head]` builds `Std.List`'s. Literals keep a fixed meaning, and the example writes `Cons(head, Nil)`.
- **Labels on symmetric operations.** `bit_xor(acc, other)` failed the label rule, since both parameters are `Wrapping[UInt64]`. Labels there would be noise, so a declaration can mark parameters positional-only with `_` (DESIGN §6).
- **Labels never reorder arguments.** The checker had to decide whether `append(back: ys, front: xs)` is allowed. It isn't: labels confirm the declaration order and never change it, so every call reads the same way.
- **`result` collides with a parameter.** `or_fail(result: ...)` made the spec name `result` shadow the parameter. The parameter is renamed; `result` and `self` are reserved in specs (DESIGN §6.1).
- **Prelude names have home modules.** `import Std.Text (String)` has to mean something, so `String` is defined in `Std.Text` and the prelude points there.
- **The wildcard rule applies inside the standard library too.** `zip_with` and `span` had `case _ =>` over `List`, which is a local type from the standard library's own point of view. They now list the cases.

## What running the examples found

Running the examples (prototype step 3) turned up:

- **`02_lists.clk`'s doc examples were never valid.** They used list literals like `[1, 2]` with functions over the module's own `List`. Once doc examples were type-checked, the checker rejected all five. They now build lists with `Cons`. This is the strongest argument for checking examples as code: written as comments, they were wrong from the start, and nothing noticed.
- **Two types can print the same.** The first message for that mistake was "expected `List[_]`, found `List[_]`". Mismatch messages now module-qualify exactly the names that clash: "expected `Examples.Lists.List[Int]`, found `Std.List.List[_]`".
- **A runtime without types needs a few facts from the checker.** `Wrapping(14695981039346656037)` must be 64-bit wrapping arithmetic, but the value alone doesn't say so. The checker hands the interpreter each integer literal's type. The one gap is generic code (`sum[N: Num]`'s `0`), handled by promotion; a compiler would use dictionaries or monomorphization (DESIGN §8).
- **Everything else ran as written:** all 27 doc examples, the STM ledger (which gives the same result on every run), and the word counter, including its error paths.

## What verifying the examples found

Verifying every example (prototype step 4) proves 87 obligations, and 15 deliberately buggy programs in `test/unverified/` are each refuted with a counterexample. What it took:

- **No example's own code was wrong.** Every spec in the examples held as written. That's less impressive than it sounds: the examples' specs are modest.
- **Library specs carry the proofs.** The calculator's lexer couldn't verify until `Std.List.span` stated what it guarantees: the prefix and rest rebuild the input, the prefix satisfies `keep`, and the prefix is nonempty when the first element passes. With those, `lex`'s termination and `digits_to_int`'s precondition are automatic. Writing specs for the standard library is the real work.
- **Specs need identity, not `==`.** `span`'s postcondition compares lists of a generic `A`, and `==` would demand `A: PartialEq`. It's also wrong for floats (NaN). Specs now use `identical(a, b)` (DESIGN §2.2).
- **One hint, as designed.** `insert`'s multiset postcondition needs a second step of `multiset`. The verifier's failure said "add `unfold multiset`", and that one line fixed it (DESIGN §4.1).
- **Refinements through `fold` work without abstract refinements.** In `06_trace.clk`, `let start: Cents = 0` is enough for `fold`'s accumulator to be a `Cents` throughout: the step function owes a `Cents` and the result is one, by parametricity (DESIGN §2).
- **Nonlinear arithmetic was no trouble so far.** `price * quantity >= 0` and `total * 10 + digit_value(d) >= 0` are proved with sign facts and no hints.
- **The verifier found a checker bug.** A punned record field (`{ value }`) recorded its own type at the record literal's span, overwriting the record's type. Nothing before step 4 read that table closely enough to notice.

## What checking effects found

Step 5 made effect rows part of every function type, and gave the verifier effect parameters, TVar state, invariants, and handler clauses. All examples and the standard library verify: 101 obligations. Nine more deliberately buggy programs in `test/unverified/` are refuted, and twelve more programs in `test/reject/` are rejected. What it found:

- **The ledger's spec was false.** `move_to_savings` promises the total doesn't change. That's not true of a `Ledger` whose `checking` and `total` are the same TVar, and nothing in the type ruled that out. The counterexample, `Ledger(TVar#1, TVar#0, TVar#1)`, shows the aliasing. (It first printed as `Ledger(TVar, TVar, TVar)`, which hid exactly the part that mattered, so counterexamples now number the values of opaque types.) The fix went in the type: each field is refined `where not identical(...)`, and `open_ledger` proves that, since new TVars are distinct. This is the first time the verifier found a real bug in an example, and it was in the example with the most careful spec (DESIGN §5).
- **Step 4 had two soundness bugs, which step 5 exposed.**
  - *A refinement on an argument's type hid the refinement on its type argument.* After `savings` became `TVar[Cents] where ...`, writes to it stopped owing `Cents`. The verifier looked for `TVar[...]` and didn't look through `where`. Nothing failed: an obligation just disappeared. That's the most dangerous way a verifier can be wrong, and it took a change elsewhere to notice.
  - *Code after a `handle` could be treated as dead.* If the handled expression doesn't return (`fail(...)`), the verifier concluded the whole `handle` didn't, and skipped every obligation after it. But a handler can return instead. `test/unverified/handled_failure.clk` now covers both.
- **Without frame conditions, callers know nothing.** After a call to an `Stm` function, nothing is known about TVars beyond the callee's postcondition. Even a read-only helper has to say `ensures read(x) == old(read(x))` for each TVar it leaves alone. The examples don't hit this, but the first test of invariants at a call did. It's now open question 8.
- **Effect parameters had been documentation.** `Http`'s doc comment said `get` requires `url.host == host`, but nothing checked it. Now the operation declares it as a precondition, and the verifier proves it at each call: trivially in `10_order_sync.clk`, where the URL is built with the literal host. `count_file`'s `Fs[read: path]` is now checked as well, at the `read_bytes` call inside `map_failure`'s function argument.
- **The effect signatures in the examples were already right.** Turning on the effect checker rejected nothing in the examples or the standard library. Effect clauses were the part of the examples written most carefully, because they're the reviewable surface.
- **The effect checker settles what step 2 couldn't.** `attempt`'s error type is decided by what the function passed to it performs, so constraints on such types are now solved. One left on an unknown type is an ambiguity error, rather than being silently dropped.
- **A function used as a value can't keep an effect parameter that names its argument.** `map(paths, read_bytes)` needs `Fs[read: any]`, because `read_bytes`'s `Fs[read: path]` names a parameter that doesn't exist until there's a call. This fell out of the representation rather than being designed. It's the right answer, and it's now recorded in DESIGN §3.

## What the first adversarial review found

Another LLM, as an adversarial reviewer, found 42 problems in round 1 (`../../Review.md`, answered in `../../Response.md`). Seventeen were soundness bugs where the verifier proved something false about runtime behavior, each with a small program that verified and then misbehaved. None was caught by the test suite I'd written, which shared my blind spots. The lessons that changed the design:

- **Facts must be scoped.** What a callback or a handled computation established was assumed afterwards, though it might never have run. This is the mirror image of step 4's "code after a `handle` is dead" bug.
- **Parametricity doesn't survive effects.** "A generic function can only produce `B`s from the `B`s it's given" is false once an operation, a primitive, or a TVar can supply one (DESIGN §2).
- **Refinements on invariant type constructors need equivalence.** `TVar[Cents]` passed as `TVar[Int]` broke every TVar refinement, so a TVar's refinement is now part of its type (DESIGN §5).
- **Per-value invariants need ownership.** Shared TVars, construction anywhere, and nesting each let code assume an invariant nobody established (DESIGN §5).
- **Proof code must be held to proof rules.** An effectful lemma, a lemma recursing without a measure, and an unfolding outside its precondition each proved `false`.
- **Tests need to be pinned.** Accepting "the solver gave up" as a refutation, unpinned lines, and unchecked counts let tests pass for the wrong reasons.

Of the 42, 40 are fixed or adopted, and two completeness gaps are deferred (#23, part of #24). No example program needed changing. `09_sorting.clk` relies on `Ord`'s totality, which a type variable now gets only from its class constraint.

## What the second round found

Round 2 confirmed the round-1 fixes and found ten more problems (#43–#52), eight of them soundness bugs with reproducers. Most were in the round-1 fixes themselves, in exactly the places I'd flagged as weakest. The pattern was the same each time: a rule stated in DESIGN, implemented as a syntactic approximation that covered the obvious shape and missed the rest.

- **Ownership by syntax** recognized `write(x.f, ...)` only when the TVar's solver term still mentioned `x` (it doesn't for a value just built), and only for TVars that were direct fields. Now an invariant type may hold TVars only as direct fields, and writes are attributed from the syntax.
- **"Returning" included only normal return.** A failure caught inside the same transaction committed a broken invariant. Leaving abnormally now counts as an exit.
- **Parametricity, again.** Round 1 restricted what may be *assumed* of a type variable's refinement. But a `TVar[Cents]` makes the refinement something *owed* too, in the other direction, and class methods (`negate`) and operators are sources of new values.
- **"Some argument shrinks" isn't a termination argument.** It has to be the same one at every call.
- **A guard and a well-formedness check are two halves of one rule.** With both missing at once, `type Fixed = Int where pos_id(self) == self` proved every integer positive.
- **Fail closed means deciding by the same function that assumes.** `refinedSyntax` approximated `typePred` and missed parameterized aliases. It now asks `typePred`.

## What the third round found

Round 3 confirmed round 2's fixes and found seven more problems (#53–#59), six of them Critical. Two lessons are new:
- **A fix in one direction has to be matched in the other.** Round 2 taught `instantiationSafe` that class constraints make values (#49), but the new tag path (#43) asked the same question without the class check. Both now share one function.
- **"Known to make nothing" was a claim about one class, not what it enables.** `FixedWidth` has no methods, but `Wrapping[I]` gets arithmetic under it. The exempt list is now only the comparison classes.

Three findings were older than round 2: the handler rules were missing their equivalents of rules that already held for functions. A function's result owes its `ensures`, but `resume` didn't owe the operation's. A generic function's body is checked with rigid type variables, but a generic operation's clause wasn't. And `Stm`, whose operations the verifier models as primitives, could be handled like any other effect, which meant those models could be made false.

## What reviewing visibility found

Adding `public` took four review rounds (8–11) and turned up eleven findings (#63–#73). Three of them were older than visibility, and only became reachable or visible because of it. Some lessons:
- **A new module system breaks every analysis that stopped at a module's edge.** The loader could suddenly load several user modules, so these all became wrong:
  - recursion groups, which were computed per module, so cycles between modules went unchecked (#63);
  - `verify`, which covered only the entry file (#64);
  - the module root, which came from the file path as given (#71);
  - the `Std` namespace, which any entry could claim (#68).
- **Instances are the escape hatch.** They're global, so anything an instance can do, any module can do:
  - derived instances read and built private parts (#65);
  - hand-written instances of classes without methods built values the compiler couldn't back (#69, #72, #73).

  The fix that held was to stop hand-writing those instances altogether, rather than limiting which heads are allowed.
- **"Assumed, but not checked" is unsound, not incomplete.** A class method's `ensures` was assumed at every call, and no instance was ever checked against it (#70). That had been filed as a partial feature (#8). Until instances are checked against their class, class methods can't have contracts.
- **What other modules' proofs can see is part of visibility too.** The design said "callers see only a function's contract", but the verifier unfolded any body. Now a body is visible only if it's public and names only public things, and it then counts as API.
