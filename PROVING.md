# Proving in Bend: lessons learned

Notes from building `src/nat.bend`, `src/int.bend`, `src/qext.bend` (exact
integer arithmetic and `QExt.mul_comm` from scratch, June 2026). Written for
whoever picks this up next. Everything here was learned by hitting the
checker; each pattern below appears in a file in this repo that currently
passes `All terms check.`

## Toolchain

- No `bend` binary needed: `node bend2/main.ts file.bend` from a bend
  checkout works (node 24 runs the TS directly; the JS *backend* fails under
  node, but checking and checker-normalized `main`s work fine).
- A file with no `main` just checks. A `main` returning a value is
  normalized by the checker and printed — a free, slow, trustworthy test
  harness: `def main() -> I.Int: I.Int.add(...)` prints the constructor.
- Read `guide/GUIDE.md` fully before writing anything. Read the header
  comment of `bend2/bend.ts` (first ~200 lines) for the real grammar; the
  guide glosses over details the grammar pins down.
- `tests/proof/` in the bend repo is the style reference. `add_comm.bend`
  there independently discovered the same idioms as this repo.

## The rewrite discipline (the one thing to internalize)

`%e : P` where `e : {a == b : T}`:

- `P` is the goal with `_` marking an occurrence of **`b`** (the RHS of `e`).
- The new goal is `P` with `a` (the LHS of `e`) there instead.

So `%` replaces **RHS-of-`e`** occurrences with the LHS. To rewrite
left-to-right you must `Equal.sym` first — or better, state the lemma
flipped so its RHS is the "complicated" side that shows up in goals. This
repo carries `add_assoc_rev` and flipped statements of `add_succ`,
`mul_succ`, `mul_distrib` for exactly this reason. When a rewrite "did
nothing" or produced a reflexive goal, the `_` marked the wrong side.

Motives must be written in the goal's *reduced* vocabulary: after
`case 1n+p:`, the goal's `Nat.add(1n+p, x)` has already unfolded to
`1n+Nat.add(p, x)`. When a motive fails, write out both sides by hand and
reduce each def call mentally (defs unfold transparently; `match` on a
constructor fires).

## Affinity applies to proofs

Law binders are live. If an induction hypothesis and a helper lemma both
mention `b`, you get `b (consumed more than once)`. Fix: `for +b: Nat` in
the law (fine for any `Data` type). Matching a `+` scrutinee hands out `+`
pattern fields, which you also need when the IH and another call both use
`ap`. Just mark every law binder `+` from the start; it costs nothing and
removes a whole error class.

Occurrences inside motives and in erased (`-`) arguments are dead and free.
`Equal.trans`/`sym`/`cong` erase their endpoints, so spelling them out is
verbose but never counts as a use.

## Evidence by conversion beats rewriting

If the goal is *convertible* to a lemma's statement, the lemma application
is the proof — no `%` needed:

```
case 1n+ap 0n:
  add_zero(1n+ap)   # goal was {Nat.add(Nat.sub(1n+ap,0n),0n) == 1n+ap}
```

The checker normalizes `Nat.sub(1n+ap, 0n)` away on its own. Before writing
a `%` chain, ask whether some helper's type already *is* the goal. See
`Int.add.same_comm` being called directly in `Int.add_comm`.

## Structuring tricks that worked

- **Helper laws over inline motives.** `Int.add_comm` contains no rewrites
  in its same-sign cases: the shuffle lives in `Int.add.same_comm`, proved
  once by its own small match, then applied by conversion. Every time a
  goal got big, factoring the next step into a named `law` with
  matchable parameters made it small again.
- **Push case splits into the program.** `Int.add.same` matches on the
  magnitude instead of wrapping everything in a canonicalizing `Int.mk`,
  because a `match` on a stuck variable makes conversion stuck too, and
  then proofs can't reduce past it. If a proof needs to know which branch
  an op took, the op should expose that branch as a top-level `match` on
  its parameters.
- **Canonicalize in ops, not invariants.** `Int.add` always returns
  `Int{False{}, 0n}` for zero, so `==` on results needs no "canonical"
  side conditions in laws.
- **`Equal.trans` chains for pure shuffles.** When no single rewrite
  orientation works (re-bracketing four summands in `mul_distrib`), build
  the chain explicitly. Spell the endpoints once in the calls; they're
  erased, so they're free at runtime and don't consume variables. Yes,
  it's ~20 lines where an SMT solver needs zero. That's the deal here.
- **Discrimination boilerplate, once.** Impossible `cmp` cases are closed
  by a predicate def returning `Type` (`CmpIsEQ`: `EQ{}` ↦ `Unit`, else
  `Empty`), then `%Equal.sym(Cmp, LT{}, EQ{}, e) : CmpIsEQ(_); Unit{}` —
  see `lt_ne_eq` in `src/nat.bend`. With an `Empty` in hand,
  `Empty.absurd(goal, it)` closes anything.
- **Evidence-carrying comparisons.** `Nat.cmp` returns a bare `Cmp`. The
  bridges `cmp_eq` / `cmp_gt_sub_add` (hypothesis `{Nat.cmp(a,b) == EQ{}}`
  etc. as a law parameter) are how a proof learns arithmetic facts from a
  comparison result. Any serious development needs these; expect each to
  be a small induction with two absurd cases.

## Gotchas

- **No nested matches on pattern variables** ("scrutinees in binder
  order"). Flatten: `case Int{False{}, xm} Int{True{}, ym}:` instead of
  matching the constructor fields in a second `match`.
- **Cross-module dotted names compose verbatim**: `Cmp.flip` defined in
  `nat.bend` is `N.Cmp.flip` after `import ./nat.bend as N`. Consider
  prefix-free names per file.
- **`match` scrutinees must be parameters or pattern-bound variables**,
  never computed values. Pass `Nat.cmp(xm, ym)` to a helper and match on
  the helper's parameter. This is why `Int.add.opp` takes `c: Cmp` as its
  first argument — and it makes the op *proof-friendly* for free (proofs
  can then call the helper with a literal `Cmp`).
- **No `if`**: a branch is a `match` on `True{}`/`False{}`, and there is
  no `Bool` short-circuit sugar in proofs.
- **Termination is structural, left-to-right by argument**: the recursive
  call's arguments must pass unchanged until one is a strict subterm. Put
  the decreasing argument first and keep the others literally unchanged
  (`add_assoc(ap, b, c)`, not `add_assoc(ap, c, b)` reordered by
  rewriting).
- **Parsing**: `1n+x` is sugar for `Succ{x}` and chains (`1n+1n+x`).
  `-`/`+` glued to a name starts a binder, not an operator; space your
  operators.

## Int.add_assoc campaign

How `Int.add_assoc` actually fell (int.bend 494 → 890 lines, no new Nat
lemmas needed — the ci1..ci10 inventory built for it covered everything):

- **Case split**: 8 sign patterns. fff/ttt reduce to `Nat.add_assoc`;
  ftf was the direct grind (9 cmp-combos, many absurd). fft and ttf are
  sign mirrors of each other, ground directly. The rest fell to symmetry:
  `Int.add.assoc.rev` (assoc of the reversed triple + `Int.add_comm` =
  assoc, a 5-step `Equal.trans` chain) gives tff from fft and ftt from
  ttf for free, and tft is two ttf instances plus three comms. Prove 3
  patterns directly, derive 3, reuse 2 — write `rev` before grinding.
- **A motive cannot mention a variable you still need to `match` on**
  ("scrutinees in binder order: unbound, consumed, or out of order").
  `%e : P` where `P` names `c` consumes `c`. So: `match c:` FIRST, then
  `%e` inside each branch — matching refines `e : {c == cmp(..)}` to
  `{GT{} == cmp(..)}` etc., which is what `%e` needs. Cost: the `%e`
  rewrite lines are duplicated per branch (fft.pos has 9 branches × 2).
- **sym-orientation was 100% of the ftf breakage.** `%e` replaces
  RHS-of-`e` occurrences; goals almost always contain the lemma's
  *complicated* LHS (`Nat.add(Nat.sub(xp,ym),ym)`, `Nat.sub(z,Nat.sub(y,x))`),
  so wrap nearly every ci/geometry lemma in `Equal.sym` before `%`.
  Also: `Equal.sym(T, a, b, e)` takes `e : {a == b}` and gives
  `{b == a}` — twice the fix was deleting a double-sym or swapping the
  two endpoint args, and the checker's expected/observed pair names the
  exact mismatch.
- **`cmp_add_sub` is the bridge that kills a parameter.** In fft/ttf the
  outer cmp is on `cmp(1+(xp+ym), zm)` and the inner one on
  `cmp(1n+xp, Nat.sub(zm, ym))`; instead of a third `Cmp` parameter with
  flipped evidence (the ftf.ltgt pattern), `cmp_add_sub` rewrites one
  into the other outright when `zm > ym`. Fewer helper laws, shorter
  statements.
- **The four impossible (c1, c2) combos in fft.pos/ttf.pos** all close
  by `cmp_gt_add_left` (or `cmp_gt_add` after a `cmp_eq`-transport) +
  `eq_ne_gt`/`lt_ne_gt` discrimination. Note `cmp_gt_add(a, b)` proves
  `cmp((1+b)+a, a) == GT` — the increment is the *second* argument.
- **Zero-magnitude sub-cases** (`Int.add.same`'s `Int.mk` branch): a
  `w == 0 + w` goal with `w` an `Int.add.opp` result needs the cmp
  exposed as a parameter (zl helpers), and its GT/LT branches need
  `sub_pos` to rewrite `Nat.sub(a,b)` to `1n+..` twice (once per
  occurrence) so `Int.mk` and `Nat.cmp(0n, ..)` unstuck by reduction.
- Cost reality check: the "300–500 lines" estimate below landed at +396,
  but ~120 of that is mechanical mirror text (ttf = fft with signs
  swapped) and per-branch `%e` duplication.

## Rough cost model (calibrated on this spike)

- Nat lemma (comm/assoc class): ~15 lines, minutes each once the style
  clicks.
- Discrimination bridge: ~10 lines each, write the set once.
- mul_distrib-class shuffle: ~25 lines, the trans chain is the bulk.
- Int.mul_comm / QExt.mul_comm: nearly free given the layer below (~6–60
  lines, first-try).
- `Int.add_assoc` (sign-magnitude): done — +396 lines on top of the
  truncated-sub/ordering library, inside the 300–500 estimate (see the
  campaign section above). `Rat` with gcd
  normalization needs a division correctness proof — the hardest single
  lemma on the path to the field axioms.
- Unary `Nat` is O(value) at runtime. Proofs don't care; CAD-sized
  coordinates will. A binary-nat layer is the right next investment.

## Where the trust boundary is

`All terms check.` means the (human-written, per `AGENTS.md`) kernel in
`bend2/bend.ts` accepted the proofs. The README admits the Lean
formalization lags the checker and the theory rests partly on invariants
outside the kernel. Treat the proofs as strong evidence, not bedrock, and
re-check after any compiler upgrade.
