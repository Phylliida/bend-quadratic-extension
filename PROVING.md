# Proving in Bend: lessons learned

Notes from building `src/nat.bend`, `src/int.bend`, `src/qext.bend` (laws)
and their `*_proofs.bend` counterparts (exact
integer arithmetic and `QExt.mul_comm` from scratch, June 2026). Written for
whoever picks this up next. Everything here was learned by hitting the
checker; each pattern below appears in a file in this repo that currently
passes `All terms check.`

`Int` has since been re-represented as a `(pos, neg)` difference pair, which
retired the whole `Int.add_assoc` case-analysis campaign described below. See
"Why Int is a (pos, neg) difference pair" for the measurement, and the
campaign section (kept as the record of what the previous representation
cost). The rewrite discipline, the affinity rules, the `%` orientation trap
and the termination rules are unchanged by that switch: they are properties
of the checker, not of `Int`.

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
  see `lt_ne_eq` in `src/nat_proofs.bend` (law stated in `src/nat.bend`). With an `Empty` in hand,
  `Empty.absurd(goal, it)` closes anything.
- **Evidence-carrying comparisons.** `Nat.cmp` returns a bare `Cmp`. The
  bridges `cmp_eq` / `cmp_gt_sub_add` (hypothesis `{Nat.cmp(a,b) == EQ{}}`
  etc. as a law parameter) are how a proof learns arithmetic facts from a
  comparison result. Any serious development needs these; expect each to
  be a small induction with two absurd cases.

## Laws vs proofs (the split-file mechanism, as observed)

This repo keeps laws and proofs in separate files per module
(`nat.bend`/`nat_proofs.bend`, `int.bend`/`int_proofs.bend`,
`qext.bend`/`qext_proofs.bend`). What the checker actually does, all
verified empirically on this checkout:

- **Filling**: `proofs.bend` does `import ./laws.bend as L`, then
  `def L.name(args): <proof>` fills `law name`. Dotted law names fill the
  same way: `law Int.add_comm` is filled by `def I.Int.add_comm(x, y)`.
- **Naming inside the proofs file**: the fill attaches the def to the
  *laws file's* module, so recursive and cross-proof calls go through the
  alias: `NL.add_comm(...)`, `I.Int.add.same_comm(...)`. Bare names do not
  resolve (the proofs file defines nothing under its own namespace), and
  chained aliases do not exist: `NP.NL.add_comm` is "not a defined name".
- **Third files** that want to *use* a proved law must import both the
  laws file (under the alias they call through) and the proofs file
  (under any alias — it may be unused; its presence in the import graph
  is what fills the laws). Calling an unfilled law errors with
  `a filled definition (an unfilled law is a dead claim: live code
  cannot use it)`.
- **A laws-only file does not check.** Open laws count as TODOs, so
  `node bend2/main.ts src/nat.bend` exits 1 with
  `Error: 84 TODOs found. The code is incomplete, and not a valid proof
  yet.` — and the count is transitive over imports (int.bend reports 22 on
  its own, since it imports only `Base`; qext.bend 24 = 22 Int + 2 QExt).
  This is expected; the `*_proofs.bend` files are the gates that print
  `All terms check.`
- **Defs are not laws**: a def a law *statement* needs (`Cmp.flip` in
  `cmp_antisym`, `flip_eq_lt`, ...) must live in the laws file; anything
  only proofs touch (`CmpIsEQ`, `CmpIsGT`, `NatIsPos`, `Nat.pred`) moves
  to the proofs file. int.bend used to need `import ./nat.bend as N` for
  `N.Cmp.flip` in `Int.add.opp_comm`; with the `(pos, neg)` representation
  no Int law statement mentions `Nat` at all, so int.bend imports only
  `Base` and the transitive TODO count no longer includes nat.bend.
- **Files with a `main`** that returns a value print only the normalized
  value, not `All terms check.` — scratch.bend printing
  `(src/int.Int{10n, 5n}, src/int.Int{10n, 5n})` with exit 0 *is* the pass
  signal there (both sides of `(3 + -5) + 7` land on the same non-canonical
  representative of 5, which is what `(pos, neg)` equality looks like).

## Gotchas

- **No nested matches on pattern variables** ("scrutinees in binder
  order"). Flatten: `case Int{False{}, xm} Int{True{}, ym}:` instead of
  matching the constructor fields in a second `match`.
- **Cross-module dotted names compose verbatim**: `Cmp.flip` defined in
  `nat.bend` is `N.Cmp.flip` after `import ./nat.bend as N`. Consider
  prefix-free names per file.
- **`match` scrutinees must be parameters or pattern-bound variables**,
  never computed values -- and never *let-bound* values either. Pass
  `Nat.cmp(xm, ym)` to a helper and match on the helper's parameter. This
  is why `Int.add.opp` takes `c: Cmp` as its first argument — and it makes
  the op *proof-friendly* for free (proofs can then call the helper with a
  literal `Cmp`). See the Rat section for the pending-binder rule behind
  it, and for what it costs when the thing to destructure comes out of a
  function call.
- **No `if`**: a branch is a `match` on `True{}`/`False{}`, and there is
  no `Bool` short-circuit sugar in proofs.
- **Termination is structural, left-to-right by argument**: the recursive
  call's arguments must pass unchanged until one is a strict subterm. Put
  the decreasing argument first and keep the others literally unchanged
  (`add_assoc(ap, b, c)`, not `add_assoc(ap, c, b)` reordered by
  rewriting).
- **Parsing**: `1n+x` is sugar for `Succ{x}` and chains (`1n+1n+x`).
  `-`/`+` glued to a name starts a binder, not an operator; space your
  operators. A parameterless `def` still needs its empty list: `def f() -> T:`
  parses, `def f -> T:` fails with `expected : '('` / `observed : '-'`.

## Int.add_assoc campaign (historical: sign-magnitude `Int`)

Kept as the record of what the old representation cost. Under the `(pos, neg)`
`Int` this whole campaign is seven lines (see the next section); nothing below
applies to the current `src/int.bend`. The `Nat` inventory it forced into
existence (`ci1`..`ci10`, the `cmp_*` bridges) is still in `src/nat.bend` and
is still what `Int.canon` and gcd will want.

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

## Why Int is a (pos, neg) difference pair

The trigger was `Int.mul_distrib`, which turned out to be **false** under the
sign-magnitude representation, not merely unproved. `Int.add` canonicalized
its zero (through `Int.mk`), `Int.mul` did not, so the two sides of
distributivity disagreed on the *representation* of 0:

    Int.mul(Int{True,0}, Int{False,1} + Int{True,1}) = Int{True,0}
    Int.mul(Int{True,0},Int{False,1}) + Int.mul(Int{True,0},Int{True,1}) = Int{False,0}

and it fails even for the canonical zero: x = `Int{False,0}`, y = `Int{True,3}`,
z = `Int{False,1}` gives `Int{True,0}` against `Int{False,0}`. It holds only
for nonzero x. Making `Int.mul` canonicalize through `Int.mk` fixes it, but
`Int.mk` matches on its magnitude, so `Int.mul(Int.mk(s,m), y)` is a *stuck*
term while `m` is symbolic — which then infects every composite product in
every downstream proof. Two unfolding laws (`Int.mul.mk_left`,
`Int.mul.mk_right`, stated flipped so `%e` fires left-to-right) unstick just
the existing laws; the distributivity proof itself would still need sign cases
crossed with magnitude cases crossed with cmp cases.

`Int{pos, neg}` = `pos - neg` removes the problem at the root: every operation
is a constructor, so nothing is ever stuck and no law sees a case split.

Measured on a throwaway prototype of the same five laws, before committing:

| law | `(pos, neg)` proof lines | sign-magnitude proof lines |
|---|---|---|
| `add_comm` | 7 | 13 |
| `add_assoc` | **7** | **545** (+ ~124 lines of helper-law statements) |
| `mul_comm` | 14 | 7 |
| `mul_distrib` | **17, one branch, zero case analysis** | not proved; false as stated |
| `mul_assoc` | 38 (two `Nat`-half chains + assembly) | 9 (+16 lines of `Int.mul.mk_*` unfoldings) |

The trade, stated plainly so nobody re-derives it the hard way: `Int` is now a
*presentation*, not a canonical form. `Int{1,0}` and `Int{2,1}` are both 1 and
are not `==`, so `==` no longer decides equality. That obligation moves to
`Int.canon` (a `Nat.cmp` on the two sides) plus its quotient lemma
(`canon x == canon y` iff `xp + yn == yp + xn`), and then to `Rat`
normalization. It does not disappear — it relocates to exactly the gcd
territory that was always going to be the hard part, which is the right place
for it: the ring laws are bookkeeping, and `(pos, neg)` makes them formal.

## Splitting a law into its two Nat halves

When a `Z`-level goal is two independent coordinate equations, prove the
coordinates as their own laws and assemble:

    def Z.mul_assoc(x, y, z):
      match x y z:
        case Z{xp, xn} Z{yp, yn} Z{zp, zn}:
          %Equal.sym(Nat, <pos LHS>, <pos RHS>, Z.mul_assoc.pos(xp, xn, yp, yn, zp, zn))
            : {Z{_, <neg LHS>} == Z{<pos RHS>, <neg LHS>} : Z}
          %Equal.sym(Nat, <neg LHS>, <neg RHS>, Z.mul_assoc.neg(xp, xn, yp, yn, zp, zn))
            : {Z{<pos RHS>, _} == Z{<pos RHS>, <neg RHS>} : Z}
          {==}

Each chain's `%e` annotations then spell only one coordinate instead of the
whole goal — roughly half the text — and the assembly is three lines. The
`Equal.sym` is needed to orient the half-law's equation so `%` replaces the
half-LHS with the half-RHS; state the halves either way round, but pick one
and say so in the law comment.

## Rough cost model (calibrated on this spike)

- Nat lemma (comm/assoc class): ~15 lines, minutes each once the style
  clicks.
- Discrimination bridge: ~10 lines each, write the set once.
- mul_distrib-class shuffle: ~25 lines, the trans chain is the bulk.
- Int law under `(pos, neg)`: 3–8 lines each (`{==}` when the operation is
  structural in the right way, e.g. `Int.neg_invol`, `Int.neg_add`,
  `Int.sub_eq_add_neg`); a shuffle (distributivity, associativity) is 15–40.
  Under sign-magnitude the same laws were 7–545.
- `Rat` with gcd normalization needs a division correctness proof — the
  hardest single lemma on the path to the field axioms.
- `Nat` is unary in *proof land* only. A proof-land literal is a tower of `Succ`
  around `Zero` (`bend.ts:2245`), so literal size is term size and each `Nat`
  operation recurses over that tower; the compiled lanes are binary already (C:
  `Nat` is W64, `nat_add`/`nat_mul`/`nat_divmod` are native ops; JS: BigInt).
  Proofs don't care; CAD-sized coordinates will. A binary-nat layer for proof
  land is the right next investment. (This bullet said "O(value) at runtime"
  until the correction that the runtimes are binary.)

## The Rat route: remaining plan

State at handoff (updated after the Rat normalization unit): `Int` is
`Int{pos, neg}` = `pos - neg` with all 19 ring laws proved; `Int.canon` (+
`canon.pos`, `canon.neg`, `canon.idem`, `canon.scale`) is in, and so is the
quotient lemma in both directions (`Int.canon.eqv.fwd` / `.bwd`); the Nat
scaling groundwork (`cmp_add_left`, `cmp_mul_right`, `mul_sub_add`,
`sub_of_add`, `mul_sub`, `mul_one`) is in. `src/rat.bend` has the type,
`Rat.mk`, the operations, `Rat.mk.scale`/`Rat.mk.eqv` (so `==` decides rational
equality on canonical values) and the identity laws; the Rat laws that compose
two normalized results are still open. See "Rat: what the normalization cost"
for that work's shape and its traps.

Check with (from a bend checkout):

    cd /home/bepis/prog/verus-cad/bend
    node bend2/main.ts ../bend-quadratic-extension/src/nat_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/src/int_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/src/qext_proofs.bend
    node bend2/main.ts ../bend-quadratic-extension/scratch.bend

All four must print `All terms check.` (scratch prints a value instead). The
laws-only files are *supposed* to fail with `Error: N TODOs found.`

### The target

`Rat{num: Int, den: Nat}`, canonical when `den` is positive, `num` has one
side zero (i.e. is `Int.canon`'s output), and `gcd(num.pos + num.neg, den)`
is 1. `Rat.mk(n, d)` normalizes; `==` on canonical `Rat`s then decides
rational equality.

### The key move: prove canonicality by scaling, not by coprimality

To make the field axioms work you need the **forward** direction only:

    n1 * d2 = n2 * d1  implies  Rat.mk(n1, d1) == Rat.mk(n2, d2)

Get it from `norm(n*k, d*k) == norm(n, d)` for `k >= 1`, applied to
`(n1*d2)/(d1*d2)` on both sides. That needs:

- `Int.canon.scale`: `canon(x * K) == canon(x) * K`, where `K = Int{k, 0n}`
  and `k >= 1`. (Careful: `k = 0` is a separate branch, where
  `Int.mul_zero` collapses both sides to `Int{0n, 0n}`.)
- `gcd(m*k, d*k) == k * gcd(m, d)`.
- exact-division cancellation: `div(p*k, g*k) == div(p, g)` when `g | p`.

This deliberately avoids Euclid's lemma and coprime-ness (`gcd = 1` plus
`b | a*x` implies `b | x`), which are the deep part of "gcd correctness". The
*reverse* direction — `Rat.mk(n1,d1) == Rat.mk(n2,d2)` implies
`n1*d2 = n2*d1` — is trivial, because two equal canonical `Rat`s have equal
fields. What is *not* needed anywhere is that gcd is the *greatest*.

### Nat division correctness

`base.bend` has `Nat.divmod.go(n, m, d, r)` (fuel = `n`, structural) and
`Nat.divmod(a, b) = divmod.go(a, bp, 0n, 0n)` for `b = 1+bp`. With
`b = 1+bp`, the loop state satisfies

    a = d*b + r + n        and        r + m + 1 = b

(initially `n=a, m=bp, d=0, r=0`; each step either bumps `d` and resets
`r` when `m` runs out, or bumps `r`). At `n = 0` that gives
`div(a,b)*b + mod(a,b) == a` and `mod(a,b) < b`. Project the pair with
`Nat.div.fin` / `Nat.mod.fin` — a law statement cannot destructure.

The loop invariant is the whole proof; state it as a law parameterised by
`n, m, d, r, b` with the `r + m + 1 == b` hypothesis, and induct on `n`
(structural, and `n` is the first parameter, so the descent check passes).

### Nat gcd

Euclid's descent is *not* structural, so gcd has to be fuel-driven, exactly
like `divmod.go`. Keep the fuel first so the descent check passes:

    def Nat.gcd.go(s: Nat, y: Nat, c: Cmp, x: Nat) -> Nat:
      match s:
        case 0n: 0n                       # unreachable with enough fuel
        case 1n+sp:
          match y:
            case 0n: x
            case 1n+yp:
              match c:                    # c = cmp(x, y), passed in
                case EQ{}: x
                case LT{}: Nat.gcd.go(sp, Nat.sub(y, x), Nat.cmp(x, Nat.sub(y, x)), x)
                case GT{}: Nat.gcd.go(sp, Nat.sub(x, y), Nat.cmp(Nat.sub(x, y), y), Nat.sub(x, y))

    def Nat.gcd(a: Nat, b: Nat) -> Nat:
      Nat.gcd.go(Nat.add(a, b), b, Nat.cmp(a, b), a)

Match `s` then `y` then `c` — that *is* binder order (s, y, c, x), so it is
legal; matching out of order is not. The subtractive step is what makes
scaling easy: `gcd(m*k, d*k) == k*gcd(m,d)` then follows from `mul_sub`
plus the fact that each step lowers `x + y` by `min(x,y)`, so fuel `a + b`
suffices. A `mod`-based Euclid would instead need `(m*k) mod (d*k) = k*(m mod d)`,
i.e. more division correctness.

### Idioms this work will need, restated

- **Evidence as a parameter.** A `match` scrutinee must be a parameter or a
  pattern-bound variable, never a computed value, and a body that matches a
  *stuck* `Nat.cmp` never reduces. So every lemma about `Int.canon` takes
  `c: Cmp` plus `e: {c == Nat.cmp(xp, xn)}`, and callers with no comparison
  to hand pass `c := Nat.cmp(xp, xn)` with evidence `{==}`.
- **Unsticking `Nat.sub`.** `Nat.sub(a,b)` is stuck while `a` is symbolic, so
  anything downstream of it (a `Nat.cmp`, an `Int.mk`-style match) is stuck
  too. `sub_pos` rewrites it to `1n+Nat.sub(a,1n+b)` given `cmp(a,b) == GT`,
  which makes it a constructor and lets everything reduce. This is the single
  most-used move in the existing proofs.
- **`%e : P` orientation.** `P` is the goal with `_` at an occurrence of the
  *RHS* of `e`; the rewrite puts the *LHS* there. To rewrite the other way,
  `Equal.sym` first. `Equal.sym(A, a, b, e)` takes `e : {a == b}` and gives
  `{b == a}` — get the two endpoints the right way round or the rewrite
  silently does nothing.
- **Reading errors.** For `{==}` the checker prints `expected` = the goal's
  left side and `observed` = its right side. For a `%` step it prints
  `expected` = the actual goal and `observed` = the annotation you wrote. A
  long `expected`/`observed` pair that looks identical usually means an
  annotation was transcribed with the wrong sub-term somewhere.
- **Splitting a law into Nat halves.** When a goal is two independent
  coordinate equations, prove the coordinates as their own laws and assemble
  with two `Equal.sym` rewrites; each chain then spells half as much.

### Order to work in

1. `Nat.divmod` correctness (loop invariant) and the `div`/`mod` laws it
   gives. This blocks everything else. **Done** (`divmod.go.spec`,
   `divmod.go.mod_lt`, `div_add_mod`, `mod_lt`).
2. `Nat.gcd` + `gcd` divides both arguments + `gcd(m*k, d*k) == k*gcd(m,d)`.
   **Done**: scaling (`gcd.go.scale`, `gcd.go.fuel`, `gcd_scale`) and
   divisibility (`gcd.go.divides`, `gcd.divides_lt`/`gcd.divides_gt`,
   `gcd_divides`) -- see the last section for what the divisibility half cost.
3. `Int.canon.scale`, and `Int.canon.eqv` (the quotient lemma,
   `canon x == canon y` iff `xp + yn == yp + xn`). **Done**: scaling
   (`Int.canon.scale.go`/`Int.canon.scale`) and both halves of the quotient
   lemma (`Int.canon.eqv.fwd`, `Int.canon.eqv.bwd`), on top of the Nat
   cross-sum lemmas `cross_gt_gt`/`cross_cmp` -- see the last section for the
   route that turned out to be cheaper than the plan.
4. `Rat`: the type, `Rat.mk`, canonicality by the scaling route, then the
   field axioms. **Partly done**: the type, `Rat.mk`, the normalization lemmas
   (`mk.canon`, `mk.zero`, `mk.fixed`, `mk.scale`, `mk.eqv`), the commutations
   and the identity laws are in; the laws that compose two normalized results
   are not -- see "Rat: what the normalization cost".
5. `QExt` over `Rat`: field axioms plus the inverse
   `1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2*d)`.

Commit each unit once its gate is green; do not leave a law stated but
unfilled, since that turns every dependent gate into `N TODOs found.`

## Where the trust boundary is

`All terms check.` means the (human-written, per `AGENTS.md`) kernel in
`bend2/bend.ts` accepted the proofs. The README admits the Lean
formalization lags the checker and the theory rests partly on invariants
outside the kernel. Treat the proofs as strong evidence, not bedrock, and
re-check after any compiler upgrade.

## Nat divmod and gcd: what the work actually cost

Steps 1 and half of 2 above are done; `src/nat.bend` carries the laws and
`src/nat_proofs.bend` the fills. Notes for the next attempt.

### Two bugs in the gcd sketch above

The `Nat.gcd.go` sketch in "Nat gcd" does not compute the gcd as written.

- **The GT step.** `Nat.gcd.go(sp, Nat.sub(x, y), Nat.cmp(Nat.sub(x, y), y),
  Nat.sub(x, y))` puts the difference in the *y* slot as well as the x slot,
  so the state collapses to `(x-y, x-y)` and the loop answers `x-y` or 0.
  Run on literals (a `main` returning `G.gcd(...)` prints the value; write it
  down *before* proving anything): the sketch gives `gcd(10, 4) = 0` and
  `gcd(7, 5) = 2`, and the one-token fix -- the GT step leaves y alone,
  `Nat.gcd.go(sp, y, Nat.cmp(Nat.sub(x, y), y), Nat.sub(x, y))` -- gives
  `2` and `1`. A wrong loop is cheap to find this way and expensive to find
  through a failing proof: the scaled-gcd proof below fails on the sketch's
  version, which is how it surfaced here.
- **`a = 0.`** `Nat.gcd(0, b)` with the sketch's fuel `a + b` runs the LT
  step `(0, y) -> (0, y - 0) = (0, y)`, which never progresses: it burns the
  whole fuel and returns 0, but `gcd(0, b)` is `b`. `src/nat.bend` matches on
  `a` first (`case 0n: b`) so the loop only ever sees `x >= 1` -- which is
  also what makes the fuel `a + b` *provably* enough, since every step then
  strictly shrinks `x + y`.

### The gcd scaling proof, restated

`gcd_scale` needs two loop lemmas, and the shapes are not free choices:

- `gcd.go.scale`: `go(s, y*k, cmp(x*k,y*k), x*k) = k * go(s, y, c, x)`, for
  *every* fuel (both sides run out together), no hypothesis beyond
  `c = cmp(x,y)`. Each step is two rewrites: `cmp_mul_right` to collapse the
  scaled comparison to the branch constructor, `mul_sub` to collapse the
  scaled difference. The multiplier must sit on the right of each product
  (`Nat.mul(y, 1n+kp)`), because that is the shape `cmp_mul_right` and
  `mul_sub` are stated in; the k-on-the-left spelling has no counterpart for
  `cmp` (`cmp_add_left` does not apply to a product).
- `gcd.go.fuel`: fuel above the state's own measure is harmless. State it over
  a fuel `s1` *and* the slack `t` with `(x + y) + t = s1`, and induct on
  `s1`, **not** on the slack: one loop step takes `s1 = 1 + sp` to `sp` on
  both sides while the *difference* between the two fuels rides along
  untouched, so an induction on the difference never closes.
- `Nat.gcd(m*k, d*k)` runs the loop with fuel `m*k + d*k` while
  `Nat.gcd(m, d)` runs it with `m + d`, so the two loops cannot be matched
  directly at all: `gcd_scale` is `gcd.go.scale` at the big fuel, then
  `add_mul_slack` to see that fuel as `m + d` plus a slack, then `gcd.go.fuel`
  to throw the slack away, then one `Nat.mul_comm` for the product order.
- The state's x slot has to be written `1n + xp` in `gcd.go.fuel` (and in any
  law that reuses it), because the canonical fuel `x + y` must start with a
  *constructor* or the right-hand loop is stuck on its fuel match. The cost is
  that every law of this family needs `sub_pos` to undo the loop's own
  `Nat.sub` in the GT branch before the induction hypothesis applies.

### "gcd divides both arguments": solved, and what the obstacle actually was

Proved. The laws are `gcd.go.divides` (the loop invariant), `gcd.divides_lt` /
`gcd.divides_gt` (one step each, as helper laws) and `gcd_divides` (the top
level); the fills are in `src/nat_proofs.bend`, and the shape of the witness
type in `src/nat.bend` is part of the proof, not a style choice.

The arithmetic was never the problem. The step needs the quotients and the
equations from *both* halves of the induction hypothesis's witness pair, plus
the pair back, and the checker's rules around that cost three attempts:

1. `match` refuses a computed scrutinee ("a match cannot scrutinize a computed
   value"), so the returned pair cannot be taken apart where it is produced.
   The step therefore runs inside a helper `def` whose binder *is* the pair, and
   the recursive call's result is passed straight in as that binder -- the pair
   is never destructured in place.
2. Fields of a `Sigma` are linear and each quotient/equation is needed twice, so
   the fields have to be copied. `Sigma<&2, &2, ..>` does not do it (a field's
   *own* quantity is what counts, and `Tuple`'s default is `&1`).
3. The copy spelling `+e = e` (or a `+e` pattern field) is where the checker
   stops. `+p = p` makes it *re-check the field's type*; for a `Sigma` that type
   is the dependent field `B(fst)`, which after whnf sharing arrives as
   `App(Var("_", -1, <the lambda>), fst)` -- an application whose head is a
   *cell holding a lambda*. `term_infer`'s App rule beta-steps a literal `Lam`
   head but not a cell wrapping one, so inference falls to the `default` branch
   and reports `expected : an annotated term (cannot infer) / observed : q => {x
   == Nat.mul(g, q) : Nat}`, with the span pointing at `Nat.divides`'s body --
   the lambda's own source. The check that triggers it is `check-let`'s
   `term_check(v_inf.ty, .., Typ(Qua(lhs_kind(lhs, q))))`: the `Let` is the
   re-bind, `v_inf.ty` is the field type, and inferring *that* is what dies.
   (Traced with a throwaway patched copy of the checker in `/tmp`, never
   touching `bend2/`: the diagnostic there is `console.error(new
   Error().stack)` inside `Err` plus a dump of `tm.k[j]`, `tm.v[j]` and
   `v_inf.ty` in `check-let`. That is the cheap way to localize this class of
   failure.)

Two properties of a `+field` in a hand-written `Data` ADT make all three
problems disappear, and that is what `Nat.Div` is:

    type Nat.Div<+g: Nat, +a: Nat> is Data:
      Div{+q: Nat, +e: {a == Nat.mul(g, q) : Nat}}

- a `+field` is Many *at the declaration*, so a plain pattern already yields it
  Many and no re-bind is ever written -- nothing to type-check, nothing to
  break;
- a constructor's field types mention its own earlier fields *directly*, so
  there is no family parameter applied to `fst` and no cell-headed redex is
  ever rebuilt;
- the pair itself is not copied (each half is destructured once), so
  `Nat.divides_both` can stay the `A & B` `Sigma` it was.

Two shape details that are not free choices:

- the destructure pattern must be the ADT's own constructor (`NL.Div{q, e} =
  d`); `(q, e) = d` is a `Tuple` pattern, and the checker reports "a constructor
  of Nat.Div (missing, or already matched)".
- `gcd.divides_gt`'s `d` parameter is `Nat.divides_both(g, 1n+xp, y)`, *not*
  `Nat.divides_both(g, s, y)`: `gcd.go.divides` always states the state's x slot
  as a successor, so the recursive call's first dividend is literally `1n + xp'`
  and a law stated over an arbitrary `s` cannot be fed it. The GT branch of the
  loop rewrites the goal with `sub_pos` first (replacing the stuck
  `Nat.sub(xp, yp)` with `1n + Nat.sub(xp, 1n+yp)` in both places the loop term
  mentions it) and then needs `ge_sub_add` rather than `cmp_gt_sub_add` for the
  helper's equation, since the helper's subtraction is now `xp - (1+yp)`.
  `Equal.cong(Nat, Nat, u => 1n+u, ..)` adds the successor.

Cost: `nat.bend` +~90 lines of statement and comment, `nat_proofs.bend` +~120 of
fill. The two helper laws and the loop induction were each right on the first
run once the witness type was a `Data` ADT with `+` fields.

The same trick is the general lesson: **when a proof has to use a witness twice,
give the witness a `Data` ADT with `+` fields rather than an `Exists`, and never
write a `+` re-bind.**

## Int.canon: what the scaling and quotient lemmas cost

`Int.canon.scale` (`canon(x*(1+kp)) == canon(x)*(1+kp)`) and both halves of the
quotient lemma (`Int.canon.eqv.fwd`: equal canonical forms force
`xp + yn == yp + xn`; `Int.canon.eqv.bwd`: the reverse) are proved. Notes for
whoever picks up the rest.

### Shape: thread the comparison, or you cannot case on it

`Int.canon.go`'s body matches on its `Cmp`, and `Nat.cmp(xp, xn)` is a computed
value -- not a legal match scrutinee -- so *every* law that reasons about canon
per branch takes `c: Cmp` plus `e: {c == Nat.cmp(xp, xn)}` as parameters and
spells the right-hand canon as `Int.canon.go(c, xp, xn)`. That is why
`Int.canon.scale.go` exists next to the statement anyone wants to use
(`Int.canon.scale`), which is one call with `c := Nat.cmp(xp, xn)` and `{==}`.

### Scaling is bookkeeping, not mathematics

`Int.mul(Int{xp, xn}, Int{1+kp, 0})` reduces to
`Int{add(xp*(1+kp), xn*0), add(xp*0, xn*(1+kp))}`. The `Nat.mul`-by-zero slots do
*not* reduce (`Nat.mul` matches on its first argument, a variable), so each
branch starts with `mul_zero` and `add_zero` rewrites; each of those fires in two
places at once (the `Nat.cmp` argument and `canon.go`'s own argument), which is
what a motive with the hole repeated is for. `cmp_mul_right` then collapses the
scaled comparison, the branch evidence collapses it to the constructor just
matched, and `mul_sub_right` (already in nat.bend, the right-scaled twin of
`mul_sub`) says the scaled difference is the difference of the scaled slots. The
one non-obvious spelling: `e` has to be a `+` binder, because the GT and LT
branches read it twice. An equation is `Data`, so a `+` equation binder costs
nothing -- and unlike a `+` *field* of a Sigma it is not a dependent type, so the
copy is unremarkable.

### Int.eq.pos / Int.eq.neg: constructor injectivity, and the projections it needs

`Int.canon.eqv.fwd` needs to get `a == c` out of `{Int{a, b} == Int{c, d}}`. Bend
has no injectivity rule, so it is the J axiom (`%e : P`) with a motive whose two
sides are *projections* of the two Ints:

    %e : {Int.proj.pos(Int{a, b}) == Int.proj.pos(_) : Nat}

At `_ := Int{c, d}` that motive is the goal `{a == c}`, and at the left-hand
Int it is `{a == a}`, which `{==}` closes. The projections
(`Int.proj.pos` / `Int.proj.neg`) are proof-only defs in `int_proofs.bend`; no
law statement mentions them. This is the general recipe for extracting a
constructor's fields from an equation in Bend: define the projection as a *def*
(a motive cannot contain a `match`), then use it in the J motive.

### The forward half: nine branches, two shapes

Case on `c1` and `c2`. The canon forms are `Int{sub(xp,xn), 0}` (GT),
`Int{0, sub(xn,xp)}` (LT) and `Int{0,0}` (EQ), so:

- **the two forms agree** (GT/GT, LT/LT, EQ/EQ): `Int.eq.pos` / `Int.eq.neg`
  turn the Int equation into a coordinate equation, and the goal is then Nat
  shuffling -- `cmp_gt_sub_add` / `cmp_lt_sub_add` say the coordinate is the
  difference, so both sides are "difference + common part" and the equation
  follows by reassociating.
- **they disagree** (a difference against zero, or differences of opposite
  sign): the coordinate equation says a truncated difference is `0`, `sub_pos`
  says that same difference is `1 + something`, and a successor is not zero.
  That last step is `Nat.succ_ne_zero` (`0 = 1 + a` is impossible), stated over
  `0` on the left because that is the orientation the callers build, with
  `NatIsZero` as the discrimination -- both proof-only, next to `Nat.pred` in
  nat_proofs. `Empty.absurd` then closes the branch, which is why the goal type
  has to be written out in those branches.

The one thing that cost real time here was `%`-orientation, twice per branch:
`Equal.sym(A, a, b, e)` takes `e : {a == b}` and gives `{b == a}`, and its
endpoints are *erased* -- so whatever you write as the second argument is what
ends up on the left, and the checker does not complain if it disagrees with `e`.
The reliable spelling is: to replace the goal's subterm `X` with `Y`, write the
evidence `{Y == X}`, i.e. `Equal.sym(T, X, Y, <lemma stated {X == Y}>)`.

### The backward half: proved, and the plan it did not need

`Int.canon.eqv.bwd` is in the tree (statement in `src/int.bend`, fill in
`src/int_proofs.bend`), so the two halves together are the quotient lemma. The
plan above works, but it is not the cheap route: the disagreeing branches need
neither three helper laws nor `sub_pos`/`succ_ne_zero`, and the agreeing
branches want their `add_cancel` chain *factored into Nat* rather than written
inline twice. Two moves replaced the whole thing:

- **State the whole case analysis as one lemma whose conclusion is what the
  caller refutes.** `cross_cmp` (`src/nat.bend`) concludes `{c1 == c2 : Cmp}`,
  so its own fill has no case split at all: `cmp_add_right` says adding the
  same amount to both sides preserves a comparison, so the cross sum rewrites
  `cmp(add(xp,yn), add(xn,yn))` (which is `c1`, by `cmp_add_right(xp,xn,yn)`)
  into `cmp(add(yp,xn), add(yn,xn))` (which is `c2`, same law on the other pair
  plus `add_comm`) -- congruence and commutation, no arithmetic, one `Equal`
  chain. The *caller* then refutes the equation with whichever of the six
  discrimination laws names its branch (`gt_ne_eq`, `gt_ne_lt`, `eq_ne_lt`, ...:
  the file ships all six orientations), which makes each of the six vacuities
  two lines. Compare the plan's three GT/EQ, GT/LT, EQ/LT laws, each with its
  own induction and its own `sub_pos`/`succ_ne_zero` endgame: one lemma whose
  fill is a `trans` chain beats three whose fills are case analyses.
- **Push the arithmetic down to a Nat law whose statement *is* the caller's
  goal.** `cross_gt_gt` states GT/GT as the Nat equation
  `sub(xp,xn) == sub(yp,yn)`; its fill expands both differences with
  `cmp_gt_sub_add` and cancels the common `add(xn,yn)` -- that is the plan's
  6-link chain, written once, in Nat, where no goal-orientation decision is
  left to get wrong. LT/LT is the same law with the two arguments swapped
  (`cmp_gt_of_lt` flips both evidences, the cross sum is commuted, and the
  conclusion `sub(xn,xp) == sub(yn,yp)` is exactly what the LT canon form
  holds), so the second agreeing branch costs no new mathematics either.

What is left in the Int fill is nine branches of assembly -- a `Equal.cong`
into the `Int` constructor for the two agreeing non-zero branches, `Empty.absurd`
for the six vacuities and `{==}` for EQ/EQ -- and the only thing that needs
care there is that the goal in a branch has already reduced
(`canon.go(GT{}, ..)` is `Int{sub(xp,xn), 0n}`, which is what the `cong`'s
endpoints and the `Empty.absurd` goal have to spell).

`Int.canon.eqv` as a single "iff" statement is still not in the tree: what the
two halves give is the pair of implications, and the `Rat` route consumes only
the forward one (`canon.scale`), with the reverse direction of the *quotient*
lemma coming for free because two equal canonical `Rat`s have equal fields.


### Small harness facts that cost time

- A law may conclude a pair type (`{A} & {B}`), but *inside braces* the parser
  reads `&` as the exists binder and fails on the missing `:`: a pair type
  must be written bare (`Empty.absurd(A & B, e)`) or, better, behind a `def`
  (`Nat.divides_both`), which also keeps `%` motives to a single application.
- A proof-only helper `def` must be named *bare* (`Nat.pred`,
  `Nat.succ_add_ne_zero`), not `NL.`-prefixed: an `NL.`-prefixed name lives in
  nat.bend's namespace, resolves while nat_proofs.bend is the main file, and
  becomes "a defined name is expected" as soon as another file imports it.
- `%e : P` replaces the *right* side of `e` with its *left* side. Restated as
  a rule to write code by: **to replace a goal subterm X with Y, the evidence
  must be `{Y == X}`.** Every orientation mistake in this work was forgetting
  that and reaching for `Equal.sym` in the wrong place (and `Equal.sym(A, a,
  b, e)` itself takes `e : {a == b}` and gives `{b == a}`).
- A `%` motive may mention the hole more than once, and that is how two
  occurrences of the same stuck subterm get rewritten together (`sub_pos` on
  the GT branch touches four positions in one step).
- A `%` motive that is not an equation must be written *without* braces. `{P}`
  parses as the annotation form `{x : T}` and fails with `expected ':' observed
  '}'`; `{a == b}` is the equation form. So a motive that is a bare predicate
  application (`Nat.divides_both(..)`) goes in bare:
  `%e : NL.Nat.divides_both(<hole>, ..)`.
- A destructure pattern must name the constructor the scrutinee's type actually
  declares: `(q, e) = d` only ever matches `Sigma`/`Tuple`, so a hand-written
  witness ADT needs `Div{q, e} = d`. The error when you forget is `a
  constructor of <your type> (missing, or already matched)`.
- `+field`s in a hand-written `Data` ADT are the copy mechanism that works: a
  `+` re-bind or `+` pattern field of a *Sigma* field makes the checker re-check
  the dependent field type `B(fst)`, which after whnf sharing is an application
  whose head is a share cell holding a lambda -- `term_infer` cannot see through
  the cell and reports `an annotated term (cannot infer)`. `Data` ADT `+field`s
  are Many by declaration, so a plain pattern suffices and nothing is
  re-checked.

## Rat: what the normalization cost

`src/rat.bend` / `src/rat_proofs.bend` are in the tree: the type, `Rat.mk`, the
operations (`add`, `neg`, `sub`, `mul`, `zero`, `one`), the normalization lemmas
and the identity laws. `Rat.mk.scale` (`mk(n*(1+kp), d*(1+kp)) == mk(n, d)`) and
`Rat.mk.eqv` (`n1*d2 == n2*d1` implies `mk(n1,d1) == mk(n2,d2)`) are the point
of the whole exercise -- `==` on canonical Rats decides rational equality -- and
both are proved, and so is the value keystone `Rat.mk.value`
(`num(mk(n,d))*d == n*den(mk(n,d))`) that the composing laws need. Notes from
doing it; the first three are what the value lemma hit.

### Rat.mk is match-free on purpose, and that is what makes it provable

`Nat.div`/`Nat.gcd` are total functions, so the normalization needs no case
split of its own:

    Rat.mk.go(np, nn, d) = Rat{Int{div(sub(np,nn), g), div(sub(nn,np), g)}, div(d, g)}

for `g = Rat.g(np, nn, d) = gcd(sub(np,nn) + sub(nn,np), d)`, and `Rat.mk(n, d)`
just destructures `n` and calls it. Nothing in the definition matches on a
comparison, so the result is a constructor whose fields are `div`/`gcd` terms
and never a stuck `match`. Every case split therefore lives in the laws, where
the comparison can arrive as a parameter (`c: Cmp` with its evidence) exactly as
`Int.canon` does it. The numerator it produces is the difference pair
`sub(np,nn), sub(nn,np)`, which has one side zero by construction -- that is the
"canonical shape" the rest of the file assumes, and it costs nothing.

### A def application reduces only through its *arguments*, so laws go in the `go` spelling

This is the trap that decides the shape of every Rat statement. Empirically (a
two-line law with a `{==}` fill shows it): `T.mk(T.mk2(x), 2n)` reduces to
`T{T.mk2(x), 2n}` -- the body is a constructor, so substituting is enough --
while `Rat.mk(Rat.num(np,nn), d)` does *not* reduce to the same thing as
`Rat.mk.go(sub(np,nn), sub(nn,np), d)`: `Rat.mk` destructures its argument, so
what it sees is the difference pair's *own sides* re-used as raw coordinates,
not the pair `(np,nn)`. Two consequences, both load-bearing:

- The scaling lemma is stated over `Rat.mk.go` and *raw coordinates*
  (`mk.go(mul(np,1+kp), mul(nn,1+kp), mul(1+dp,1+kp)) == mk.go(np, nn, 1+dp)`),
  i.e. exactly what `Rat.mk(Int.mul(n, Int{1+kp,0}), d*(1+kp))` reduces to once
  the `Int.mul`'s two zero products (`mul_zero`, `add_zero`) have come off. The
  wrapper `Rat.mk.scale` is then three `Equal.cong`s and one call.
- The fixed point of `mk` -- "canonical" for this representation -- is stated
  *not* about a Rat but about a numerator pair: `Rat.mk.fixed` proves
  `mk(Rat.num(np,nn), 1+dp) == Rat{Rat.num(np,nn), 1+dp}` from
  `gcd(Rat.mag(np,nn), 1+dp) == 1` and a comparison, with `sub_diag` (the double
  truncation of a one-sided pair is a no-op, at the given comparison and at the
  swapped one) as the bridge. The identity laws (`mul_one`, `add_zero`, ...)
  then take the *fixed-point equation itself* as their hypothesis
  (`for +fx: {Rat.mk(n, d) == Rat{n, d} : Rat}`), which makes their fills three
  lines each and keeps the double-sub bookkeeping in one place.

### `%`, as the checker actually enforces it

The rule from the earlier sections, restated as the thing to write code by, now
confirmed against the error messages: **the evidence must be `{new == old}`**
(the old term is the one currently in the goal), the annotation `P` is the
*current* goal with `_` at an occurrence of the evidence's **right** side, the
checker verifies `P`-with-the-right-side against the goal and makes the new goal
`P`-with-the-left-side. A step that "did nothing" or produced a reversed goal is
almost always an evidence orientation (`Equal.sym`'s endpoints are erased, so
whatever you write as the second argument is what ends up on the left); two
branches of `mk.scale.num` were exactly that, and the error message names it
(its `expected` shows the goal, its `observed` shows your annotation with the
*hole filled in*).

### Scaling: split the law into its Nat halves, or drown in motives

Normalization is a Rat of three Nats, so a motive over a whole Rat is ~500
characters per rewrite and there are a dozen rewrites per branch. The way out is
the "splitting a law into its two Nat halves" trick from earlier in this file,
generalized: `mk.scale` is *three* Nat laws (`mk.scale.num`, `.neg`, `.den`),
each with a one-term goal, plus an assembly law of three rewrites. `.neg` is
`.num` at the swapped comparison (one call, after commuting the two arguments of
each gcd's sum with `add_comm`), so only `.num` and `.den` are real work, and
each branch is short: `cmp_mul_right` collapses the scaled comparison,
`mul_sub_right` (GT) or `sub_of_lt` (the other side) collapses the scaled
difference, `gcd_scale` collapses the scaled gcd, and `div_scale` says the
scaled quotient is the unscaled one. The EQ branch needs `div_self` (both sides
are `d/d`) and `div_zero` (a `div(0, d)` with a *variable* divisor is stuck --
that is why `div_zero` is a law and not a reduction).

### Exact division: uniqueness, not correctness

`div_add_mod`/`mod_lt` give quotient-and-remainder; the normalization needs the
other direction, and the whole content is *uniqueness*:

    div_unique: d1*b + r1 == d2*b + r2, r1 < b, r2 < b  =>  d1 == d2

-- a structural induction on `d1` needing no division correctness at all, only
cancellation and ordering. The step's peel (`Nat.mul` of a successor puts the
common factor *inside* the summand) is its own law (`add_assoc_cancel`), and the
vacuous branches are `lt_ne_add` (`a < b` and `a = b + s` is impossible:
`cmp_add_right` moves it to `cmp(s,0)`, which `cmp_lt_zero` refutes -- no sub,
no induction). `div_exact` is then one call, `div_exact_mul` its scaled form,
and `div_one` the gcd = 1 case.

### Witnesses: `Pair.fst`, not destructuring

`div_scale` and `divides_pos_wit` are stated over a `Nat.divides(g, a)` *binder*
rather than over `(q, e)` because the caller's witness comes out of
`gcd_divides`, i.e. it is a field of a computed pair, and a computed pair cannot
be destructured where it is produced (the `Nat.Div` ADT fixed the *other* half
of this problem -- a pair that arrives as a parameter -- and `Pair.fst` fixes
this one: it takes one component out of the Sigma `Nat.divides_both` returns
without any destructure). If a future lemma needs a second component, that is
`Pair.snd` with the same type arguments, and no annotation is needed.

### Cross-file proof helpers: the naming rule, verified

A `*_proofs.bend` file defines nothing under its own namespace, so a helper that
another file must call has to be written with the *laws* module's prefix:
`def Nat.wit_q(...)` in `nat_proofs.bend` is exported as the key `Nat.wit_q`,
which an importer reaches as `Nat.wit_q` (not `nat.wit_q`, not `N.wit_q`).
`def NL.div_self_scale(...)` -- the fill spelling -- is exported as
`nat.div_self_scale`, so it is *not* reachable from another file at all. Two
consequences worth knowing before designing a helper:

- a helper meant for callers must be defined with the laws-module prefix;
- the cheapest alternative is to make it a *law* in the laws file and fill it,
  which is what `div_self_scale` did.

Two corollaries for the value lemma, both hit and confirmed this session:

- **A law binder's type may only mention names an *earlier binder* introduced.**
  `for w: {p == Nat.mul(g, q) : Nat}` is rejected with `a defined name /
  observed : q` -- a quotient invented in the statement is not writable. So the
  value step has to take its quotients as *binders* and their equations as
  further hypotheses, and the caller reads the quotient off a `Nat.Div` at the
  one point where the goal determines its type parameters (the fill's own
  binder, i.e. `NL.Div{q, we} = w` in a `def NL.<law>(...)`).
- **`Nat.div` gets rewritten where it appears in `Nat.divmod.go` form, not as
  `Nat.div`.** A `%` step whose annotation spells `Nat.div(p, g)` reports
  `expected : Nat.div.fin(Nat.divmod(p, g))` and does nothing. `Equal.cong` over
  a variable's argument is the reliable spelling.

Verified by listing the loader's export keys (import the `.bend` file under
`node` with `bend2/main.ts` registered and read `Object.keys(m.default)`).

### The value keystone, and the three checker rules it had to satisfy

`Rat.mk.value` is landed: `num(mk(n,d))*d == n*den(mk(n,d))`, the cross product
`Rat.mk.eqv` consumes and therefore the one bridge every law that composes two
normalized results crosses. The stack under it, bottom to top:

- `Nat.div_cross`: `div(p,g)*d == p*div(d,g)` given `p = g*q` and `d = g*r` --
  the quotients are binders and the divisor is a *variable* with a positivity
  hypothesis, so a caller whose divisor is a computed gcd does not have to
  re-spell its goal as a successor first. Its fill does that rewrite once
  (`pos_witness`) and then both divisions collapse with `div_exact`.
- `Int.mul_scale`: `Int.mul(Int{xp,xn}, Int{d,0}) == Int{xp*d, xn*d}`. A shape
  law, not a ring law -- it is what turns the raw scaling spelling (the one
  `Rat.add`/`Rat.mul` write) into the coordinate pair the value equation is
  provable coordinate-wise in.
- `Rat.mk.value.go`: the value equation in mk.go's coordinate spelling, two
  `div_cross` calls per branch. The two coordinates are not the same proof: the
  gcd's dividend is `mag = P + Q` (the difference pair's own sides, one always
  0), so `g | P` is only in hand once the comparison says which side is zero.
- `Rat.mk.value`: two `Int.mul_scale` bridges around `.go`, with the witnesses
  handed in as `Pair.fst`/`Pair.snd`.

Three checker rules decided every shape above; none is in the language docs.

- **A match must head its body, and its scrutinee must still be *pending*.**
  `body_flatten` resets the pending list at every `let` to that let's own names,
  and `match_flatten` errors -- "match scrutinees in binder order (this variable
  is unbound, consumed, or out of order: reorder the match)" -- once the list
  runs out. So the scrutinee must be a parameter or a field bound by an earlier
  case/destructure *of the same body*, and the match cannot be preceded by
  unrelated `let`s. This is why the case split is the first thing in
  `Rat.mk.value.go`'s fill.
- **A `let`-bound value can never be destructured**: `w = Pair.snd(..)` followed
  by `Div{q, e} = w` is rejected with "a match cannot scrutinize a local binder
  (give it its own def)". A witness that comes out of a *call* therefore has to
  reach its destructure as a **parameter** -- that is the whole reason
  `Rat.mk.value.go` takes `wm`/`wd` as binders (and `div_scale`,
  `divides_pos_wit`, `div_pos_wit` take theirs the same way), and the caller
  hands in `Pair.fst`/`Pair.snd` of the pair `gcd_divides` returns.
- **A family application is not `Data`, so it cannot be a `+` binder.** A
  copyable binder of type `Nat.divides(g, a)` is rejected with `expected : Data /
  observed : Type`: a parameterized family never unfolds to its ADT node (the
  angle-bracket `Nat.Div<g, a>` spelling is the one that does). Witnesses are
  linear binders -- and that is fine, because the *fields* of `Nat.Div` are
  `+fields` (Many), so what a proof reads twice is the quotient and the
  equation, and a witness it needs again is rebuilt from them: `N.Div{dr, dwe}`.
- On `div_cross`, confirmed once more: the `%` hole marks an occurrence of the
  evidence's **right** side, so the evidence has to be written `{new == old}`.
  `Equal.sym(A, a, b, e)` with `e : {a == b}` yields `{b == a}`, and getting the
  two endpoints the wrong way round is reported with the two orientations side
  by side (`expected : {d == ..}` / `observed : {.. == d}`).

### What is left

`Rat.mul_assoc` is in, and it is the template for the rest. Four notes from
doing it, all load-bearing for the siblings:

- **The composing laws must be stated over `Rat{Rat.num(np,nn), 1n+dp}`** --
  the difference pair -- with the comparison as a parameter. The obvious
  alternative (inputs `Rat{n, 1n+dp}` with a fixed-point hypothesis `fx`) does
  not survive contact with `Rat.mk.value`: that law's right side names the
  numerator in `Rat.num` spelling, and `Rat.num(np,nn)` is a *different pair*
  from `Int{np,nn}` (`Int{sub(np,nn), sub(nn,np)}`, one side zero). Relating
  the two needs the sign, which `fx` does not hand over (`fx` only says
  `numof(mk(n,d)) == n`, i.e. `n` is the div/gcd term, not a difference pair).
- **The product of two difference pairs is one again, but that is a theorem.**
  `Rat.num.mul` proves `Int.mul(Rat.num(np1,nn1), Rat.num(np2,nn2)) ==
  Rat.num(U, V)` (U, V the product's own coordinates) by nine branches: which
  side of the product vanishes is exactly the sign of the two factors, so the
  two comparisons come in as parameters and each branch derives the zeros with
  `sub_of_lt` at the flipped comparison and closes with `dp.eq.right` /
  `dp.eq.left`. With it, a value equation's difference-pair numerator can be
  replaced by the raw product and `Int.mul_assoc` applies. Without it the whole
  route is stuck: `R1*zn == xn*R2` is simply *false* for raw pairs (take
  `xn = Int{5,3}`, `yn = Int{1,0}`, `zn = Int{1,0}`: `R1*zn = Int{2,0}` but
  `xn*R2 = Int{5,3}`).
- **The assembly is a cancellation, not a substitution.** The denominators the
  value equations carry are *normalized* (`a = div(d1,g1)`), so
  `A*d1 == R1*a` and `B*d2 == R2*b` do not hand over the composed cross product
  directly: both sides are scaled by the factor the two denominators share
  (`yd`, since `d1 = xd*yd` and `d2 = yd*zd`), the two sides meet at the single
  middle product, and `Int.scale.cancel` (with `Nat.mul_right_cancel` under it)
  takes the factor off again. `Int.scale_cross` is that law; its fill is one
  `%` step per rewrite -- split the scales with `Int.scale.pair` and walk them
  past the factors they must sit next to with `mul_swap`/`mul_assoc`/`mul_comm`
  -- which is affordable only because the statement is letters, not spelled-out
  fractions.
- **A constructor literal cannot head a `let`** ("an annotated term (cannot
  infer)"), and `+x: T = v` does not parse, so a proof that wants to name a
  scaled unit binds a def application instead: `def Int.unit(n) = Int{n, 0n}`
  exists for exactly that. Likewise a comparison a law needs twice must be a
  `+` binder (`for +c: Cmp`), or the fill is rejected with "consumed more than
  once".

Still open, in dependency order: the other composing laws (`add_assoc`,
`add_exchange`, `mul_distrib`, `mul_add_left`, `neg_add`, `neg_neg`). They need
one thing `mul_assoc` did not: an `Int.add` numerator is a *sum* of coordinates,
so the `Rat.num`-of-a-sum facts (and the `Int.canon` projections under them)
have to be stated before the same four-call fill can be written. Then `QExt`
over `Rat`.

### The composing laws: what `neg_neg` actually costs (measured, not guessed)

The attempt to land the siblings went one law deep and stopped, and the reason
is worth writing down before anyone re-pays for it: **`neg_neg` is not the
one-congruence law it looks like, and `mk`'s output is not the difference pair
the composing laws are stated over.** Two concrete findings, both from running
the checker.

**1. A composing law cannot be stated directly over an operation's output.**
The first draft of `Rat.neg_neg` was

    for +c: Cmp, +np, +nn, +dp ... {Rat.neg(Rat.neg(Rat{Rat.num(np,nn), 1n+dp})) == Rat{Rat.num(np,nn), 1n+dp} : Rat}

and `{==}` does *not* close it: the goal's left side is `mk(neg(neg(A)), d)` with
`A = numof(mk(neg(Rat.num(np,nn)), d))` -- a `div`/`gcd` pair, not
`sub(np,nn), sub(nn,np)` -- and `Int.neg_invol` cannot be applied to it because
the inner `Rat.neg` did not produce `Rat{neg(Rat.num), d}`, it produced
`mk(neg(Rat.num), d)`, whose fields are `div(sub(...), G)`. Measured directly:
the `{==}` fill was rejected with the goal `Rat{Int{div(divmod(...)), ...},
div(...)}` against the observed `Rat{Int{sub(np,nn), sub(nn,np)}, 1n+dp}`.

So the siblings need the identity laws' *own* hypothesis -- `mk(n,d) == Rat{n,d}`
for the value in hand -- or a lemma that discharges it. The parent's read is
confirmed: without that bridge the composing laws are unreachable from the
canonical statements the layer's own identity laws use.

**2. The bridge is `Rat.mk_idem`, and it *is* provable.** The useful form is not
`mk(n,d) == Rat{n,d}` (that needs coprimality of `mk`'s output, the deep part
this route avoids) but

    Rat.mk(numof(mk(n,d)), denof(mk(n,d))) == mk(n,d)

-- `mk` is the identity on its own output, stated over `numof`/`denof` because
that is exactly what a caller holds after an operation. Its proof is
`Rat.mk.eqv.raw` at the cross product `mul(numof(M),denof(M)) == mul(n,denof(M))`,
which is `Rat.mk.value`'s own equation once `Int.mul(x, Int{k,0})` is unfolded
with `Int.mul_scale` -- i.e. *no coprimality and no case split*. Two dead ends
found on the way (both cost time, both are avoidable):

- the `Nat` half is not free: `denof(mk(n,1+dp)) = div(1+dp, G)`, so the equation
  `mul(G,q) == 1+dp` that `div_scale`/`mul_right_cancel` want has to be *built*
  (`div_exact` at the gcd witness' quotient, then `pos_witness` on `G` and a
  congruence on `mul(u,q)`), and it is needed on both sides.
- `Rat.mk` **destructures its argument**, so a numerator spelled through another
  function (`Int.sub(Int{np,0n}, Int{0n,nn})`) is *seen differently* from
  `Int{np,nn}`: `mk` sees `add(np,nn), 0`, not `np, nn`. An `Int` value that is
  going to be handed to `mk` must be spelled `Int{np,nn}` exactly, which also
  means it *cannot be a `let`* ("an annotated term (cannot infer)" for a
  constructor literal) -- it has to be written inline at every mention.

**3. Two checker facts that cost the most time here, neither documented before.**

- **A proof-only `def` in a `*_proofs.bend` file must be annotated**: `def F(x)`
  with a bare parameter list works *only* when `F`'s name is a law in the book
  (that is the fill mechanism). For any other helper the parameter list needs
  types, and a dependent binder type forces a return annotation too --
  `def NL.f(g: Nat, a: {p == q : Nat}) -> Nat:` parses; the same without
  `-> Nat` fails with `expected : '->' / observed : ':'` pointing at the *def*
  line, which reads like the body is at fault and is not.
- **Reaching a law's fill from another file is not the same as calling the
  law.** Probing with a file that imports both `nat.bend` (as `N`) and
  `nat_proofs.bend` (as `NP`), *all four* spellings of a proved Nat law --
  `N.mul_assoc`, `NP.mul_assoc`, `Nat.mul_assoc`, `nat.mul_assoc` -- were
  rejected with `expected : a defined name`, even though
  `rat_proofs.bend` calls `N.sub_diag` and friends successfully. Inside its own
  file the fill's own spelling (`NL.mul_assoc`) is what resolves. Do not assume
  a law key is callable by its laws-module name; check with a one-line probe.
  `Pair.fst`/`Pair.snd` for their part only infer when spelled *inline* with
  `Nat.divides(...)` type arguments at the call site -- binding the
  `gcd_divides` pair to a `let` first makes the type argument fail with
  `expected : Data / observed : Type`.

Next step for the next round, in order: land `Rat.mk_idem` (statement in
`rat.bend`, fill in `rat_proofs.bend`, using `Int.mul_scale` + `Rat.mk.eqv.raw`
and the `Nat` equation built with `div_exact`/`pos_witness`), then `neg_neg`
(one `Equal.cong` on `Int.neg_invol` after the `mk_idem` rewrite), then
`neg_add` (a cross product through `Int.neg_mul`), and only then the
associativity/distributivity four -- whose `Int.add` numerator also needs the
sum form of `mk_idem`'s right-hand side, so budget for a `Rat.num`-of-a-sum
family there.

### `Rat.mk_idem` is a *statement* problem, not a fill problem (measured)

A round was spent on the `mk_idem` statement above and it does **not** go
through as handed over: everything in its fill lands (the comparison, the
`mk.value` cross product, `eqv.raw`'s two positivity slots) except the one step
the handover described as bookkeeping -- the *positivity* of `denof(M)`. The
tree was left green with the law and its fill removed; nothing about the route
below is a fill bug, and three separate spellings of it were tried and measured
against the checker.

**1. `mk(Rat.num(np,nn), d)` is `mk(Int{np,nn}, d)` in everything but the cross
product's right-hand side.** `mk` destructures its argument, and when the
argument is `Rat.num(np,nn)` -- i.e. `Int{sub(np,nn), sub(nn,np)}` -- the fields
`mk.go` receives are the pair's *own sides*, so:

    numof(mk(Rat.num(np,nn), d)) = Int{div(sub(np,nn), G), div(sub(nn,np), G)}
    G                            = gcd(add(sub(np,nn), sub(nn,np)), d)

i.e. `G` is `Rat.g(np,nn,d)` **unexpanded**, and `denof(M) = div(d, Rat.g(np,nn,d))`.
This is the measurement that kills the "bridge" framing: `Rat.mk.den.pos(np,nn,dp)`
is stated at *exactly* that gcd, so `mk.den.pos` looked like it should apply
verbatim -- and it does not, because of the fit rule in (2).

**2. A type-level `Rat.mag(A, B)` is not the same term as `Rat.mag(np, nn)`, and
the checker will not fit them.** `mk.den.pos`'s conclusion prints its gcd as
`gcd(add(sub(np,nn),sub(nn,np)), 1n+dp)` -- the *unexpanded* magnitude, because a
`def` applied to concrete arguments is only forced one level in a type -- while
the goal's denominator carries the *expanded* one,
`gcd(add(sub(sub(np,nn),sub(nn,np)), sub(sub(nn,np),sub(np,nn))), 1n+dp)`. The
two are equal (one `sub_diag` per coordinate: the second at the comparison with
the arguments swapped, `cmp_antisym` + `Cmp.flip`), but `div_pos_wit` and
`Equal.cong` both *fit* rather than unify, so the equation cannot be transported
across the `Nat.div` the two spellings sit under. Building the evidence at the
term the goal actually has is not available either: the witness for `g | 1n+dp`
has to come from `gcd_divides` at the *same* magnitude, and its conclusion is
stated at whatever spelling the caller passes -- so the caller is back at (2).

**3. No congruence seems to reach under `Nat.div`** (this is the load-bearing
new fact, and it generalizes far past this law): `%` expands `Nat.div` into
`Nat.divmod(x,y).fin` form *before* rewriting, and in `Equal.cong` the
substitution of the argument lands **after** that expansion, so the two ends of
the congruence differ by the shape of the substituted argument. Measured on a
two-line probe with no Rat in it at all:

    Equal.cong(Nat, Cmp, u => Nat.cmp(0n, Nat.div(1n, ZZ(u, v))), a, a, {==})

is rejected with `expected : ... ZZ(Nat.add(np,nn), ...)` against
`observed : ... ZZ(Nat.sub(np,nn), ...)` -- the ends disagree in the *argument*,
not in the division. So `Rat.gden` was introduced as a named head
(`def Rat.gden(np,nn,d) = Nat.div(d, Rat.g(np,nn,d))`) on the theory that a named
application substituted one level at a time would keep the ends equal; it does
not change the outcome (same mismatch, printed with the substituted argument).
Two more spellings were rejected on the way and are worth not re-trying:
`Cmp.flip(c)` as a value anywhere (let value, local binder, argument, clause
kind, def return type) is `expected : a defined name` -- the *only* producer of a
flipped comparison is a lambda body whose binder is a variable, i.e. a cong whose
lambda **is** `N.Cmp.flip`; and the lambda's type arguments in `Equal.cong` must
be written out (`Nat, Cmp`, not `Cmp, Cmp`) or the binder comes back typed `Cmp`.

**What the next round should try, in order.** (a) State `mk_idem` with the
positivity of `denof(M)` as a *hypothesis* and let the caller supply it (the
caller holding an operation's output has `mk.den.pos` at its own value, so the
hypothesis is exactly what it can write) -- this needs no new Nat lemma and no
transport; (b) if the law must be self-contained, give `mk` a *variant* whose
cross product names the numerator in the *expanded* spelling
(`Int{div(sub(np,nn),G), ...}` rather than `numof(M)`), proved by the same
coordinate argument as `mk.value.go` -- i.e. extend `mk.value` with a second
statement rather than trying to bridge to the first; and (c) only then
`neg_neg`, which is two congs once `mk_idem` exists (the whole reason the
composing laws need it). Note for (b): `mk.value`'s own fill is content to take
`pd` as `{==}` because its `d` is a successor literal; `mk_idem`'s `d` is
`denof(M)`, which is why its positivity is the whole difficulty.

### mk_idem landed, and the "no congruence under Nat.div" rule is too strong

`Rat.mk_idem` **is** in, and **unconditional**:
`mk(numof(M), denof(M)) == M` for `M = mk(Rat.num(np,nn), 1n+dp)`, with the
comparison as the only parameter. `Rat.mk_idem.raw` is the same identity with a
general denominator plus the two positivity hypotheses (`pd`, `pq`) that a
caller with a product denominator needs. `Rat.neg_neg` is in too (below).

The two steps the previous round could not discharge are one call each, and both
were a *spelling* problem rather than a missing lemma:

- **The positivity of `denof(M)` is one `div_pos_wit`** at the gcd spelling the
  *goal* carries -- `Rat.g(P, Q, d)` for `P = sub(np,nn)`, `Q = sub(nn,np)`, the
  raw coordinates `mk` destructured -- with the witness `gcd_divides` returns
  for that same magnitude:

      N.div_pos_wit(G, dp,
        Pair.snd(N.Nat.divides(G, R.Rat.mag(P, Q)), N.Nat.divides(G, 1n+dp),
          N.gcd_divides(R.Rat.mag(P, Q), 1n+dp)))

  Nothing is transported. `Rat.mk.den.pos`'s conclusion is at the *unexpanded*
  `Rat.g(np, nn, 1n+dp)`, i.e. a different spelling of the same gcd -- that, and
  not the law's truth, is what the previous round measured when it found that
  `mk.den.pos` "looked like it should apply verbatim and does not". A caller of
  `mk_idem.raw` whose value is `mk(Int{U,V}, d)` gets the same fact the same way
  (`gcd_divides(Rat.mag(U,V), d)`), which is exactly how `Rat.mul_assoc` already
  derives its two denominators' positivity.
- **The numerator spelling** (`mk.value` names `Rat.num` of the raw coordinates;
  the statement is written over the difference pair) is two `sub_diag`s, one at
  the comparison and one at the flipped one -- reachable by `Equal.cong` because
  they sit under `Nat.mul`/the `Int` constructor, not under `Nat.div`: the same
  two rewrites `mk.fixed`'s fill already makes, with the same flip evidence.

**Correction to the previous round's load-bearing claim.** "No congruence seems
to reach under `Nat.div`" is too strong. `Equal.cong` *with an explicit motive*
transports all four of these, each measured with `All terms check.` (probe file
deleted; the text is the whole probe):

    def divarg(a: Nat, g: Nat) -> {Nat.div(Nat.sub(a, 0n), g) == Nat.div(a, g) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, g), Nat.sub(a, 0n), a, N.sub_zero(a))

    def divarg2(+U: Nat, +V: Nat, g: Nat)
      -> {Nat.div(Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), g) == Nat.div(Nat.sub(U, V), g) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, g),
        Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(U, V),
        N.sub_diag(Nat.cmp(U, V), U, V, {==}))

    def divdvs(a: Nat, +U: Nat, +V: Nat, +d: Nat)
      -> {Nat.div(a, N.Nat.gcd(Nat.add(Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(V, U)), d))
          == Nat.div(a, N.Nat.gcd(Nat.add(Nat.sub(U, V), Nat.sub(V, U)), d)) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(a, N.Nat.gcd(Nat.add(u, Nat.sub(V, U)), d)),
        Nat.sub(Nat.sub(U, V), Nat.sub(V, U)), Nat.sub(U, V),
        N.sub_diag(Nat.cmp(U, V), U, V, {==}))

    def divsucc(+d: Nat, +a: Nat, G: Nat, e: {d == 1n+a : Nat})
      -> {Nat.div(1n+a, G) == Nat.div(d, G) : Nat}:
      Equal.cong(Nat, Nat, u => Nat.div(u, G), 1n+a, d, Equal.sym(Nat, d, 1n+a, e))

i.e. (a) a rewrite of `Nat.div`'s dividend, (b) `sub_diag`'s shape inside that
dividend, (c) a rewrite inside the gcd that *is* the divisor, (d) the dividend's
successor re-spelling that `div_pos_wit` concludes at. What fails is the `%`
spelling measured before: a `%` step whose annotation does not match the goal
after `Nat.div` has been expanded (the two ends then disagree in the *argument*).
So the usable rule is: reach for `Equal.cong` with a motive, not `%`, when a
`Nat.div` is in the way. Two consequences worth having: deriving `pq` inside
`mk_idem.raw`'s fill (a variable denominator, so the *witness type* has to be
re-spelled from `divides(G, d)` to `divides(G, 1+ap)` -- an evidence-type
rewrite, which is why the raw form keeps the hypothesis), and a proof of the
representative lemma below.

### `Rat.neg_neg` (landed) and what it costs

The unconditional difference-pair statement is **false**, evaluated:

    neg(neg(Rat{Rat.num(4,0), 2})) = Rat{Int{2,0}, 1}   vs   Rat{Rat.num(4,0), 2} = Rat{Int{4,0}, 2}

`==` on `Rat` is structural, so negation of a non-canonical term comes back
mk-headed with div/gcd fields. With coprimality (`Rat.mk.fixed`'s own
hypothesis, which the identity laws' `fx` also carries) the law is two
`mk.fixed` calls around one congruence: `neg` of `Rat{Rat.num(np,nn), 1+dp}` is
`mk` of the swapped pair, whose gcd is the stated one because `Rat.mag` is
symmetric by `add_comm` -- so the intermediate is a fixed point too. No value
equation and no case split: negation never touches the denominator.

### The additive composing laws: the statement is true, the obstruction is the numerator representative

Measured, so that the next round starts from the right place:

- `add_assoc` and `neg_add` (over `Rat{Rat.num(np,nn), 1n+dp}`, no coprimality)
  are **true**: at `x = 2/3, y = -3/5, z = 5/4` both sides of each evaluate to
  the same `Rat` (`Rat{Int{79,0}, 60}` and `Rat{Int{0,1}, 15}`).
- The obstruction is not `mk_idem` and not positivity. An `Int.add` numerator is
  a *sum* of two difference pairs, and `Rat.mk.value`'s right-hand side names it
  as `Rat.num(U, V)` of the sum's raw coordinates -- which for a mixed-sign sum
  is a pair with **both** sides non-zero, i.e. a *different representative* of
  the same integer from the raw pair the `Int` ring laws see. At
  `add(2/3, -3/5)` the sum's raw coordinates are `(10, 9)`, evaluated:

      Rat.num(10, 9) = Int{1, 0}        Int{10, 9} = Int{10, 9}
      canon of both  = Int{1, 0}

  `mk.eqv.raw` consumes a cross product of raw numerators, so it can never
  equate the two: the multiplicative sibling's middle step (`Rat.num.mul`, which
  says a *product* of difference pairs is one-sided again) has no additive
  counterpart, because a sum of difference pairs is not one-sided. The bridge
  the additive family needs is at the level of the value, not of the cross
  product:

      Rat.mk(Rat.num(U, V), d) == Rat.mk(Int{U, V}, d)

  ("mk is blind to which representative of the numerator's value it is handed").
  Its *statement* is true at exactly the ambiguous point above -- evaluated:
  `mk(Rat.num(10,9), 3)` and `mk(Int{10,9}, 3)` both print `Rat{Int{1,0}, 3}` --
  and its proof should be the shapes measured in this section: one `divarg2` per
  coordinate, plus the gcd/divisor transports. **The rest of this paragraph is
  an argument, not a measurement.** With it, each additive law should read as
  the mul_assoc recipe the other way round (rewrite the side whose numerator is
  raw into the `Rat.num` spelling, then consume the two value equations with
  `mk.eqv.raw`), and `pq` for such a side is the four-line `div_pos_wit` call
  above -- also verified at the raw spelling, for a caller whose value is
  `mk(Int{U,V}, 1+ap)` rather than `mk(Rat.num(np,nn), ·)`.

Next, in order: (1) the representative lemma above; (2) `neg_add` from it (the
negated value equation is one `Int.neg_mul` plus `Rat.num` of the swapped pair);
(3) `add_assoc`/`add_exchange` (needs the two summands' `Rat.num.mul`-style
shapes as well); (4) `mul_distrib`/`mul_add_left`; (5) `QExt` over `Rat`.

### The additive block: three units in, and the composite bridge that is still missing

Committed, each with the whole gate set green:

- **`Rat.mk.rep`** -- `mk(Rat.num(U,V), d) == mk(Int{U,V}, d)`, unconditional
  and with no comparison parameter. The two `sub_diag`s that collapse the `mag`
  of a one-sided pair are instances at the *explicit* comparisons
  (`sub_diag(Nat.cmp(U,V), U, V, {==})` and the swapped one), so nothing has to
  be flipped in, and every rewrite is an `Equal.cong` with a motive (never a
  `%`), because all of them reach under a `Nat.div`. No witness, no positivity,
  no `div_pos_wit`: no division is ever *evaluated*, only its arguments are
  rewritten.
- **`Rat.add.value`** -- `add(mk(Rat.num(np1,nn1),1+dp1), mk(Rat.num(np2,nn2),1+dp2))
  == mk(<raw sum>, mul(1+dp1,1+dp2))`, the additive twin of the product shape.
  A sum of two difference pairs is *not* one-sided, so no `Rat.num.mul`-style
  shape law can relate it, and its cross product has to be assembled: two
  `mk.value` calls scaled into the shared denominator and merged by the Int ring
  laws (`R.Rat.add.piece`, then `R.Rat.add.cross` -- proof-only helpers in
  `rat_proofs.bend`), then `mk.eqv.raw`. What makes the raw sum reachable at all
  is that each summand's coordinates `(sub(np,nn), sub(nn,np))` *are*
  truncations, so `Rat.num(ai,bi) == Int{ai,bi}` is two `sub_diag`s -- the same
  collapse `mk.fixed`'s fill makes.
- **`Rat.neg_add`** -- `-(x + y) = -x + -y` for the canonical presentation, no
  coprimality. One `Rat.add.value` at the two negated summands, one `mk.eqv.raw`
  at the value equation `mk.value` gives after `Int.neg_mul` has moved the
  negation inside, one `mk.rep`, and four `Nat.add` commutations under the
  constructor. Negation never touches a denominator, so no scaling appears.

Two rules the fills paid for, both worth not re-discovering:

- **`Equal.sym(A, a, b, e)` is called with `(a, b)` in the evidence's own
  order, and its result is `{b == a}`** -- the argument check does not
  re-orient, so passing the pair the other way round silently produces the
  reversed equation (and the goal then fails with two enormous types). The
  discipline that works: the evidence must have type `{new == old}` read against
  the goal, so pass `(old, new)`.
- **A proof-only helper `def` is not callable cross-file.** A probe importing
  `rat_proofs.bend` and calling `R.Rat.add.piece` is rejected with
  `expected : a defined name` -- the same wall the law keys hit. Fills that call
  helpers must live in the file that defines them, so `neg_add` was probed by
  editing `rat_proofs.bend` directly rather than in a scratch file.

**The four remaining additive laws all hit one bridge that is not in yet: a
*composite* representative problem, one level up from the one `mk.rep`
closes.** The shape of it, at `add_assoc` (this derivation is an argument, not a
measurement -- nothing below was run):

    LHS = add(add(x,y), z)    RHS = add(x, add(y,z))

The inner sum is `M1 = mk(S1, d1)` with `S1` a raw pair whose coordinates
`(P1, Q1)` are *sums* of scaled truncations, and the outer add reads
`numof(M1)`; the left side is therefore `mk(nL, k1*zd)` with
`nL = numof(M1)*zd + r3*k1`. The value equations (`mk.value` on each composite)
name those projections in `Rat.num` spelling, and the cross product `mk.eqv.raw`
would want is

    [Rat.num(P1,Q1)*zd + r3*d1] * xd*d2  ==  [r1*d2 + Rat.num(P2,Q2)*xd] * d1*zd

-- an equation between two *pairs* of equal value and different representative:
`Rat.num(P1,Q1)` is `Int{sub(P1,Q1), sub(Q1,P1)}`, while the right-hand side is
built from the raw `r1 = Int{a1,b1}`. And unlike the summands of
`Rat.add.value`, `P1` and `Q1` are **not** truncations, so `sub_diag` cannot
collapse them; `mk.rep` does bridge exactly this gap, but only where the pair is
the *argument of an mk*, not where it sits inside a sum. (The gap itself is the
one already measured above: `Rat.num(10,9) = Int{1,0}` against
`Int{10,9} = Int{10,9}`.) Note also that `Rat.add.value`, as it stands, needs
*both* summands spelled `mk(Rat.num(np,nn), 1+dp)`; `add_assoc`'s outer add has
one mk summand and one constructor summand, so that law does not apply to it
verbatim.

**What the next round should try, in order.** This is a plan, not a
measurement; the first item is the one that looks cheap now.

1. **`Rat.mk.canon`: `mk(X, d) == mk(canon(X), d)`**, with the comparison as a
   parameter. It looks like *two* steps: `canon(X) == Rat.num(Xp,Xn)` up to the
   comparison (both are `Int{sub(Xp,Xn), sub(Xn,Xp)}`, and `canon`'s one-sided
   form is exactly that pair), so one `Equal.cong` over the constructor puts the
   goal at `mk(Rat.num(Xp,Xn), d)`; and then `Rat.mk.rep` is that statement
   verbatim. With it, "two pairs of equal value have equal mks" follows from the
   already-proved `Int.canon.eqv.fwd` (cross-sums give `canon X == canon Y`),
   which is the bridge the four laws need. `mk.eqv.raw` cannot see it on its
   own: `mul(X, unit d) == mul(Y, unit d)` is simply false for two different
   representatives, so no cross product will ever close these laws.
2. The "mixed" value law for `add` -- one summand an mk, the other a
   constructor, which is the shape the outer add of `add_assoc` really has. It
   should go through by the `add.value` recipe, with the composite's equation
   spelled in `Rat.num(P1,Q1)` (that is what `mk.value` hands over) and the
   constructor's in its raw `Int{ai,bi}`.
3. Only then `add_assoc`/`add_exchange` themselves, and then
   `mul_distrib`/`mul_add_left`, which have the same composite shape with a
   product as the outer operation.

### `Rat.mk.canon.go` landed; the planned name was taken, and the fill is two steps

Item 1 of the plan above is in, under the name **`Rat.mk.canon.go`** --
`Rat.mk.canon` was already the *fixed-point* law (`mk.go(np,nn,1+dp) ==
Rat{Rat.num(np,nn),1+dp}` under coprimality), so the new law's name had to
differ; `.go` is the file's marker for a comparison-threaded coordinate
spelling (`Int.canon.go`, `Rat.mk.go`, `mk.scale.go`, `mk.value.go`), which is
exactly what this is:

    law Rat.mk.canon.go:
      for c: Cmp, +xp, +xn, +d, +e: {c == Nat.cmp(xp,xn)}
      {Rat.mk(I.Int{xp,xn}, d) == Rat.mk(I.Int.canon.go(c,xp,xn), d) : Rat}

The planned fill ("a cong putting canon(X) where `Rat.num(Xp,Xn)` sits, then
`mk.rep` verbatim") is right, with one orientation detail: what the cong needs
is `Rat.num(xp,xn) == canon.go(c,xp,xn)`, i.e. the *branch value* of `canon.go`
spelled as the difference pair, and the two are the same pair because the
branch's own sign forces one truncation to zero (GT: `sub(xn,xp) = 0` by
`sub_of_lt` at the flipped comparison; LT: `sub(xp,xn) = 0`; EQ: both, via
`cmp_eq` + one cong + `sub_self`). `Rat.mk.rep(xp,xn,d)` then closes it read
backwards. No positivity, no divisibility witness, no case split on a gcd:
every rewrite is an `Equal.cong` over the `Int` constructor.

One checker detail paid for by the fill: a **let-bound `Equal.cong` needs an
expected type**. `+ev = Equal.cong(Nat, I.Int, u => ...)` is rejected with
`expected : an annotated term (cannot infer)` (the motive's codomain is the
cong's second type argument and nothing determines it), while the same cong
inline as an argument of `Equal.trans`/another `cong` is fine, because the
endpoints of the surrounding term fix it. So the congs live inline; only the
`Equal.trans` chains (whose endpoints are all spelled) are let-bound.

Measured state after this commit: `rat.bend` alone 188 TODOs (was 187), the
other three unchanged (nat 124, int 32, qext 34), and all five gates green.

### `Rat.add.value.mixed`: the mixed summand, and what it actually costs

Landed: **`Rat.add.value.mixed`** -- `add(mk(Rat.num(np1,nn1), d),
Rat{Rat.num(np2,nn2), 1+dp2})` is `mk` of the unreduced sum, with each summand's
numerator scaled by the *other* summand's denominator. This is the shape
`add_assoc`'s outer add really has (one mk summand, one constructor summand), and
it is the second item of the plan above.

Two things about the statement are load-bearing, and both were decided by what
the fill can reach:

- the mk summand is named by the **presentation's** coordinates `(np1, nn1)`,
  because mk destructures `Rat.num(np1,nn1)` into the truncations
  `(sub(np1,nn1), sub(nn1,np1))` -- and being truncations, their own
  diagonal is a `sub_diag` away from vanishing, which is exactly what makes the
  cross product close. (That is the difference from the *composite* case: the
  coordinates of a sum of two difference pairs are not truncations of anything,
  so no `sub_diag` applies there. The mixed law is not the composite bridge.)
- `d` is a general Nat with two hypotheses (`pd`: `d` positive, `pq`: the
  *output's* denominator positive), the same pair `Rat.mk_idem.raw` takes and for
  the same reason: `div_pos_wit` concludes at the successor spelling of its
  dividend, so the output denominator's positivity cannot be derived for a
  variable `d`, and a caller at a product denominator (`d = xd*yd`) supplies it
  with its own `gcd_divides` + `div_pos_wit`, exactly as `Rat.mul_assoc` does.

The fill is **one helper plus one `mk.eqv.raw`**, and the helper is pure Int ring
permutation around the mk summand's own value equation:

    (A*Y + C*k1) * (d*Y)  ==  (R*Y + C*d) * (k1*Y)

with `A` the projection (`numof`), `R` its difference pair (`Rat.num(P1,Q1)`),
`C` the constructor's numerator, `Y = 1+dp2` and `k1 = denof(M1)`. Push each
outer scale into its sum (`mul_add_left`), turn each pair of scales into one
(`Int.scale.pair`, read backwards), apply the value equation scaled by `Y*Y`, and
the two sides meet. The only "new" facts are two `sub_diag`s putting the raw pair
`Int{P1,Q1}` where `Rat.num(P1,Q1)` sits (the same collapse `Rat.mk.fixed`'s fill
makes, and legal because they sit under the constructor, not under a `Nat.div`).

Measured: it lands with no truncation case split, no coprimality and no scale of
the goal itself; the rat gate is green, `rat.bend` alone reports 189 TODOs.

### `Rat.mk.eqv.val`: "mk is determined by the value", and why a cross sum

Landed: **`Rat.mk.eqv.val`** -- for positive `d1`, `d2`,

    Rat.mk(Int{xp,xn}, d1) == Rat.mk(Int{yp,yn}, d2)
      whenever   xp*d2 + yn*d1 == yp*d1 + xn*d2

This is the general quotient lemma, and it is the item the additive block was
actually blocked on: `Rat.mk.eqv.raw`'s hypothesis is a cross *product* of the
two numerators as pairs, and that equation is simply **false** for two different
representatives of one value. Measured: `6/24` and `-14/24` (the two sides of
`add_assoc` at `2/3, -3/5, 5/4`) have equal value, and their numerators `(6,20)`
and `(0,14)` give `(144,480)` against `(0,336)` -- equal as integers, different
as pairs. So no rearrangement of cross products can close the additive laws; the
hypothesis has to be the value equation read as Nats, which is
`Int.canon.eqv`'s own cross-sum shape and what the value equations of the
composing laws can actually produce. (The forward direction of
`Int.canon.eqv` is the one whose *conclusion* is that cross sum, but the
direction consumed here is `bwd`, from the cross sum to the equality of the
canonical forms; both were needed in the end, which retires the note in
`int.bend` that "nothing downstream needs the reverse direction".)

The fill is five steps per side and they are all spelled in `rat_proofs.bend`:

    mk(Int{xp,xn}, d1)
      -> mk(Int{xp,xn}, da)                    pos_witness (da = 1 + (d1-1))
      -> mk(mul(Int{xp,xn}, db), D)            Rat.mk.scale by db, read backwards
      -> mk(Int{xp*db, xn*db}, D)              Int.mul_scale (the raw spelling)
      -> mk(canon.go(cx, xp*db, xn*db), D)     Rat.mk.canon.go
      -> mk(canon.go(cy, yp*da, yn*da), D)     Int.canon.eqv.bwd, one cong

with `D = da*db`, and the right side the same chain with the denominators
exchanged; the right chain is then read backwards by one `Equal.sym`. Two
checker facts the fill paid for:

- **the `Int.mul_scale` step is not optional.** `Nat.mul` matches on its *first*
  argument, so `Int.mul(Int{xp,xn}, Int{db,0n})` is stuck at
  `Int{add(xp*db, xn*0), add(xp*0, xn*db)}` -- `mul(a, 0)` is not definitional,
  `mul_zero` is a law -- and the term therefore does *not* convert to the raw
  pair the canonical laws are stated over. `Int.mul_scale` is the only bridge,
  exactly as its own comment says.
- **a let-bound `Equal.cong` has no determined type** (the motive's codomain is
  the cong's own second type argument and nothing fixes it: `+e = Equal.cong(...)`
  is rejected with `expected : an annotated term (cannot infer)`), while the same
  cong inline in an argument position of `Equal.trans`/`Equal.sym` is checked
  against the endpoints spelled there. So the fills write their congs inline and
  bind only the `trans` chains. A related trap: a **bare constructor literal**
  cannot be let-bound either (`+R = I.Int{P1, Q1}` is rejected the same way, and
  `+R: I.Int = ...` is a syntax error), so literal pairs are written where they
  are needed, or bound as an application (`Int.mul(Int{..}, Int.unit(..))`).

Measured: rat gate green, `rat.bend` alone reports 190 TODOs. With `mk.eqv.val`
and `Rat.add.value.mixed` in, `add_assoc` has all of its pieces except the cross
sum itself -- the (★) equation below -- which needs one Nat law for the
truncation cross sum (`sub(a,b) + b == sub(b,a) + a`) and the criss-cross
combination of two of them.

### The two Nat laws the additive block needs, and why they are Nat laws

Landed, each with its fill: **`Nat.sub_cross`** and **`Nat.cross_add`**.

    sub_cross:  (a - b) + b == (b - a) + a              [comparison threaded in]
    cross_add:  A + t == A' + t' and B + t == B' + t'  =>  A + B' == A' + B

`sub_cross` is the *only* place the sign information of an arbitrary pair of
naturals is consumed, and it is the bridge between a pair and its own truncation
pair -- the shape the canonical coordinates of a sum of two difference pairs
have. Its fill is three branches, each two existing facts (`cmp_gt_sub_add` /
`cmp_lt_sub_add` for the non-zero side, `sub_of_lt` for the zero one, `cmp_eq` +
`sub_self` in EQ); the comparison is a parameter because the fill cases on it,
and callers pass `Nat.cmp(a, b)` with `{==}` evidence, so **no caller ever
case-splits**.

`cross_add` is the criss-cross combination: two equations with a common padding
determine the difference of their left-hand constants. In integers both
hypotheses read "A - A' = t' - t" and "B - B' = t' - t", so A - B = A' - B'; Nat
has no negative values, so the statement is over the two padded equations and the
fill pads both sides by `t + t'` and cancels with `add_cancel`. Its fill is the
one place with real shuffling (three `add_assoc`/`add_comm` steps per side to
reach `(A + t) + (B' + t')`), which is why it is a law and not an inline chain.

Neither is a Rat law, and they are here because the alternative -- deriving the
sign facts inside each Rat fill -- is exactly the case analysis the whole
`Rat.mk` design avoids: `Rat.mk` is match-free so that all sign analysis can be
threaded in as a parameter, and these two laws are what that buys for the
additive block. Both are unconditional, both take their comparisons (or nothing)
as parameters, and both are green: nat gate green, `nat.bend` alone 126 TODOs
(was 124), `rat.bend` alone 192, the other two counts unchanged.

### `Rat.mk.trunc`: the bridge for a *composite* numerator

Landed: **`Rat.mk.trunc`** -- `mk(Int{U,V}, d) == mk(Rat.num(sub(U,V), sub(V,U)), d)`.

This is the piece the plan's item 1 was after, and it turns out **not** to need
the comparison parameter at all. `Rat.mk.canon.go` threads one in because it is
stated in `canon.go`'s own spelling; but the pair
`(sub(U,V), sub(V,U))` *is* canon.go's branch value (one side is zero), and
`sub_diag` reaches the collapse at the two explicit comparisons `Nat.cmp(U,V)`
and `Nat.cmp(V,U)` -- so the same content is available with no case analysis
whatsoever, which is what a fill can actually use. (`mk.canon.go` is still the
right tool inside `Rat.mk.eqv.val`, where the canonical forms have to be compared
through `Int.canon.eqv`; the two laws are the same fact in the two spellings the
two consumers need.)

Why a *new* law rather than `mk.rep`: `mk.rep` collapses the mag of a one-sided
pair, and a **sum of two difference pairs is not one-sided** -- its coordinates
are not truncations of anything, so `sub_diag` has nothing to bite on. Its
*canonical* coordinates, on the other hand, are exactly `(sub(U,V), sub(V,U))`,
and that is what this law names. With it, a value whose numerator is an
operation's output -- `Int.add` of two scaled difference pairs, which is what
`add(add(x,y), z)` hands the outer `add` -- is one step from the presentation
`Rat.add.value.mixed` and the composing laws are stated over.

The fill is `mk.rep`'s fill with the two representations exchanged: four
`sub_diag` instances collapse `sub(sub(P,Q),sub(Q,P))` to `P` and
`sub(sub(Q,P),sub(P,Q))` to `Q` (two per coordinate, chained), one cong pair
carries that into the gcd's sum, and the three divisions and the numerator pair
follow by congs. Every rewrite is an `Equal.cong` with a motive, because each one
reaches under a `Nat.div`; measured: rat gate green, `rat.bend` alone 193 TODOs.

**What `add_assoc` still needs.** With `mk.trunc` in, the left-hand side of
`add_assoc` can be put in the mixed law's shape, and the mixed law's conclusion is
spelled in the coordinates `(P1, Q1)` of the inner sum -- the truncation pair --
so the cross sum `Rat.mk.eqv.val` wants is a *pure Nat* equation in
`P1,Q1,P2,Q2,xp,xn,yp,yn,zp,zn,Xd,Yd,Zd` (no `div` anywhere: the mixed law's fill
already consumed the value equations). It reduces to

    P1*Zd + zp*Xd*Yd + Q2*Xd + xn*Yd*Zd == P2*Xd + xp*Yd*Zd + Q1*Zd + zn*Xd*Yd   (★)

times the common factor `Xd*Yd*Zd`. (★) follows from exactly two instances of
`sub_cross` -- `P1 + (xn*Yd + yn*Xd) == Q1 + (xp*Yd + yp*Xd)` and the same for
`P2, Q2` -- scaled by `Zd` and `Xd` respectively and combined with `cross_add`:
the padded equations are `A + t == A' + t'` and `B + t == B' + t'` with
`A = P1*Zd + xn*Yd*Zd`, `t = yn*Xd*Zd`, `A' = Q1*Zd + xp*Yd*Zd`, `t' = yp*Xd*Zd`,
and `B = P2*Xd + zn*Yd*Xd`, `B' = Q2*Xd + zp*Yd*Xd` with the *same* `t, t'` -- so
`cross_add` gives `A + B' == A' + B`, which is (★). Scaling the two cross sums by
`Zd*Xd*Yd*Zd` instead (i.e. by `(Zd*F)` and `(Xd*F)` with `F = Xd*Yd*Zd`) makes
`cross_add`'s conclusion *be* the cross sum `Rat.mk.eqv.val` consumes, with the
common factor already distributed -- that is the one remaining Nat law, and the
fill of `add_assoc` is then: `mk.trunc` + `mk.rep` to re-spell the inner sum, one
`Rat.add.value.mixed` per side, two `sub_diag` congs to collapse the mixed law's
`sub(P1,Q1)` spellings, the Nat law above, and `Rat.mk.eqv.val`. Nothing else was
measured here: the paragraph is a derivation, not a run.

### `Rat.add_assoc` landed, and the sketch's last step needed one more shuffle

Landed: **`Rat.add_assoc`** -- `(x + y) + z = x + (y + z)` for the canonical
presentation `Rat{Rat.num(np,nn), 1n+dp}`, with no coprimality hypothesis and
**no comparison parameter** (nothing is cased on: every `sub_diag` and
`sub_cross` instance is called at an explicit `Nat.cmp` with `{==}`), exactly
the shape `Rat.mul_assoc` has. The decomposition of the last section was right
in outline -- `Rat.mk.trunc` + `Rat.add.value.mixed` per side, the two
`sub_diag` congs on the mixed law's `Nat.sub(P1,Q1)` spellings, the cross sum
from two `Nat.sub_cross` instances through `Nat.cross_add`, closing at
`Rat.mk.eqv.val` -- and it needed no new Nat law. Five things about it were
only visible once the fill was written, and four of them cost an iteration
each:

- **`Nat.cross_add`'s conclusion is not grouped the way `mk.eqv.val`'s pairs
  are.** The scaled instances give `(x1 + x3) + (x2 + x4)`: the two summands
  of one inner sum in each group. The cross sum wants `(x1 + x4) + (x2 + x3)`,
  because `TLp` pairs the *first* summand with the *third* (`P1*Zd + a3*d1`)
  and `TRn` the second with the first. So the "re-association" the sketch ends
  with is really a four-term exchange (`x1 + (x3 + (x2 + x4))` -> ... ->
  `(x1 + x4) + (x2 + x3)`, five `add_assoc`/`add_exchange`/`add_comm` steps,
  the helper `R.Rat.nat.exch4`), and on the mirrored side the same exchange
  plus one `add_comm`. This is not avoidable by choosing the padding
  differently: the only summand both instances carry is the middle one, so the
  padding is forced, and with it the grouping.
- **The two scale factors have to be chosen together.** `cross_add`'s padding
  `t` and `t'` are single terms, so the two scaled instances must share them
  *as spelled*. Scaling the first instance by `Zd*D` and the second by `Xd*D`
  (with `D = Xd*(Yd*Zd)` the common denominator `mk.eqv.val` is finally called
  at) makes the two paddings `(b2*Xd)*(Zd*D)` and `(b2*Zd)*(Xd*D)` -- equal
  after re-associating and commuting `Xd` with `Zd` (`R.Rat.nat.pad`, four
  steps). A uniform scale does not work at all: the paddings would be `b2*Xd*S`
  and `b2*Zd*S`, two different terms with no equation to respell one into the
  other.
- **The inner sums must be re-spelled before anything else touches them.** The
  raw pair an operation writes is `Int.add(Int.mul(num, unit), Int.mul(num,
  unit))`, whose coordinates contain `mul(x, 0n)` terms that are *stuck*
  (`Nat.mul` matches on its first argument), so `sub_cross`'s instance would
  have to be stated at a spelling that first needs four zero collapses; and
  `P1 = sub(Up,Un)` computed at that spelling is not the `P1` the plan's
  equation is written in. Two `Int.mul_scale` congs under one cong on mk's
  argument (one per summand) put the inner sums in the clean coordinates
  `(U,V)`, after which `sub_cross` applies verbatim. That is inference from the
  stuck shapes, not a measurement -- the clean-first route was taken from the
  start.
- **`%`'s `_` marks exactly the occurrence of the evidence's RHS.** An
  annotation whose `_` sits *inside* a wrapper (`{Nat.add(x1, _) == ...}` when
  the whole side is the RHS) does not fail loudly: the checker reports
  `expected : <the real goal type> / observed : <what the annotation demanded>`
  (i.e. `expected` is the goal, `observed` is the demand), which reads backwards
  until one notices. Two steps were spent on this, both time in
  `exch4`/`split`.
- **`Nat.mul_add_left` and `Nat.mul_distrib` are stated flipped** (`sum ==
  product`), so folding a sum into a product is the direct `%mul_add_left`
  while unfolding needs `Equal.sym` -- and `Equal.sym(A,a,b,e)` wants `(a,b)`
  in the *evidence's* order. `Nat.mul_assoc` and `Nat.add_assoc` are the other
  way round (`(a*b)*c == a*(b*c)`), so their `sym`s are the re-associations.

One measurement worth recording for the next unit: **a third file cannot
import `rat_proofs.bend`.** A two-line file that imports `rat.bend as R` and
`rat_proofs.bend` and calls `R.Rat.mk` fails with

    - expected : a defined name
    - observed : R.Rat.add.piece

-- the proof-only helpers that live under `R`'s namespace (`R.Rat.add.piece`,
`R.Rat.add.mixed.cross`) are what trips it, since the same two-line test for
`nat.bend`/`nat_proofs.bend` and `int.bend`/`int_proofs.bend` checks fine. So
the Rat chain had to be developed *inside* `rat_proofs.bend` (which is where
its helpers have to live anyway); `PROVING.md`'s "a third file imports both" is
true for nat and int and false here.

Cost: `rat_proofs.bend` 1981 -> 2465 lines -- nine proof-only helpers
(`R.Rat.nat.d3/xy/pad/exch4/split/flip2/foldA/foldB/cross4`; 155 lines) plus
the 232-line fill and the comments; `rat.bend` 879 -> 915 (the law and its
comment). All five gates green, `rat.bend` alone reports **194** TODOs (was
193). Nothing in `nat.bend` changed: the Nat half of this proof is a *proof*,
not a law.

Next, on the same recipe: `Rat.add_exchange`, then `Rat.mul_distrib` and
`Rat.mul_add_left`. Each is a mixed sum plus a cross sum; the shuffle
inventory (`exch4`, `foldA`, `foldB`, `split`, `pad`) is reusable as it stands,
and `flip2` is the only piece that is specific to which two inner sums meet.

### `Rat.mul_distrib`: the route, and the two measurements that pin it

Not landed -- this is the spelled-out plan for the next unit, plus two
measurements that were *run*, and it is written down because the route is not
the additive block's and the obstruction that decides its shape is easy to
walk into.

The law is true as stated. Measured with the checker's own normalizer, at
`X = 1/2, Y = -1/3, Z = 1/5` (all three canonical presentations):

    Rat.mul(X, Rat.add(Y, Z))                    = rat.Rat{int.Int{0n, 1n}, 15n}
    Rat.add(Rat.mul(X, Y), Rat.mul(X, Z))        = rat.Rat{int.Int{0n, 1n}, 15n}

both sides reduce to the same constructor, so `==` on Rat does decide this
instance (the two sides are equal because `mk` is determined by the value, not
by computation).

**The obstruction: `Rat.mk.eqv.raw` cannot close it as written.** Same
instance, printing the mk arguments and denominators *exactly as the two
operations write them* (`B, b` the projection and reduced denominator of
`M2 = add(Y,Z)`, `B1, b1` of `mul(X,Y)`, `B3, b3` of `mul(X,Z)`):

    LHS  = mk(Int.mul(xn, B), mul(Xd, b))                 arg Int{0n, 2n}  den 30n
    RHS  = mk(add(mul(B1, b3), mul(B3, b1)), mul(b1, b3)) arg Int{6n, 10n} den 60n

    mk.eqv.raw's hypothesis, as the operations write it:
      Int.mul(Int{0n,2n}, Int{60n,0n}) = Int{0n,120n}
      Int.mul(Int{6n,10n}, Int{30n,0n}) = Int{180n,300n}      -- NOT equal

so the raw cross product fails here for the same reason it failed in the
additive block: the two numerators are different *representatives* of one
value (the LHS's is a product with a projection, the RHS's is a sum of
products of projections). Measured, and it is the one thing that has to be
decided before writing any of the fill.

**The route it leaves.** Re-spell the RHS's numerator with `Rat.mk.trunc`
before comparing -- the RHS's raw numerator is a *sum of two difference pairs*
(mk.trunc's own case), whose truncation pair is `(sub(nRp,nRn), sub(nRn,nRp))`
-- and the same instance's cross product then *does* agree:

    Int.mul(Int{0n,2n}, Int{60n,0n})       = Int{0n,120n}
    Int.mul(Int{0n,4n}, Int{30n,0n})       = Int{0n,120n}      -- equal

(the truncation pair of `Int{6n,10n}` is `Int{sub(6,10), sub(10,6)} =
Int{0n,4n}`). Measured. So the closing step is `mk.eqv.raw` after one
`mk.trunc` (plus `mk.rep`/`Int.mul_scale` for the spellings), not `mk.eqv.val`:
the cross sum `mk.eqv.val` would want is in terms of the *projections*, which
are opaque `div` terms, and every way of eliminating them from a Nat equation
runs into a factor that cannot be cancelled.

**A warning about the two measurements above.** Both were reproduced (the
cross products `Int{0,120}` against `Int{180,300}` before `mk.trunc` and
`Int{0,120}` against `Int{0,120}` after), but `mk.trunc` on the RHS numerator
alone is *not* enough in general: checked at nine further instances of the
canonical presentation (including `X=1/2, Y=-1/3, Z=1/5` itself, and one with
two-sided coordinates) the cross product with the RHS truncated and the LHS as
`Int.mul(xn, numof(M2))` is equal at exactly one of them
(`X=1/4, Y=-5/3, Z=5/5`). So the closing step is *not* "`mk.eqv.raw` after one
`mk.trunc`" as the text below says; either both numerators have to be
canonicalized first, or the comparison has to be made between the coordinate
*pairs* rather than the raw numerators. Whoever takes this next should measure
the closing step before writing the fill -- the two sides of the identity the
fill actually proves are unambiguous (the coordinate equations give

    A*C + D2*E2 == G1*C + q2*dd        (A, G1, q2, D2E2 as below)

at every one of the ten instances checked), but which `Rat.mk` lemma consumes
it is not settled by the two measurements recorded here.

#### The remeasurement: `mk.eqv.raw` is refuted, and the consumer is the *value* lemma

Both spellings of `mk.eqv.raw` were re-measured at ten canonical instances and
**both fail, including at the section's own instance** -- this closes the
question the warning above left open:

- the raw cross product (`Int.mul(xn, numof(M2))` against the RHS's unreduced
  sum), and
- the truncated one (`mk.trunc`'s pair on the RHS), and
- the truncated-on-the-left spelling that had not been tried.

At `X=1/2, Y=-1/3, Z=1/5`, in the four Nats `(numerator pos, numerator neg,
denominator)`:

    LHS = mk(Int{6,10}, 12)     cross product  Int{360, 720}
    RHS = mk(Int{6,10}, 60)     cross product  Int{360, 720}

so *this* spelling agrees at the section's instance -- while the spelling the
recorded recipe names (`mk.trunc` of the RHS numerator, `Int{0,4}`) does **not**:
it gives `Int{360,720}` against `Int{240,480}`, and it is the truncation that
breaks it, because the RHS numerator's coordinates `(6,10)` are already the
truncation-free reading the value equations produce.

**Which lemma consumes the coordinate identity, by structure rather than by a
numerical probe.** `Int.mul(xn, B)` and `Int.add(Int.mul(..), Int.mul(..))` are
*already* constructor pairs -- `Int.mul`'s and `Int.add`'s bodies are
`Int{..}`-headed, so both arguments of the two closing `mk`s are `Int{a, b}`
terms and **no `Int.mul_scale` arises at the closing step at all**. That is the
structural fact the earlier rounds missed: the three-spelling trap belongs to
`Rat.num`'s difference pairs (and to `Rat.mk.scale`), not to mul-distrib, whose
numerators are ordinary products and sums of pairs. And for two `mk`s whose
arguments are constructor pairs, the closing lemma that speaks in value terms is
`Rat.mk.eqv.val` -- `mk.eqv.raw` asks for a *product* equation between the pairs
and is false whenever the two representatives differ, which is exactly what the
measurement above shows.

So the corrected recipe is: **`Rat.mk.eqv.val` at the two raw constructor
pairs**, with the hypothesis being the Nat cross sum of those pair coordinates,
and the hypothesis is the coordinate identity scaled -- which is why the
`R.Rat.value.scaled.pos` / `.neg` pair (landed, above) is the right bridge:
each call hands over exactly one coordinate equation of one value equation, at
the scale the cross sum needs. What is *not* settled, and is the next
measurement, is the exact pair of Nat equations the fill has to combine: the
cross sum is stated over `numof(M2)`'s coordinates, and `numof(M2)` is a
`div`/`gcd` term, not a difference pair, so the step that replaces it by the
inner sum's own value pair `(P2, Q2)` is a re-spelling *inside* the cross sum
and was not measured. Three numerical probes of candidate spellings disagreed
with each other under a hand-written model of `Rat.mk`, which is a sign the
model -- not the spelling -- was wrong; the honest state is that the consumer is
settled and the last re-spelling is not.

One harness note that cost time and generalizes: **a probe cannot import a
laws-only file at all.** `import ./src/rat.bend` plus a one-line `main` is
rejected with `Error: 195 TODOs found.` before anything runs, and the same file
importing `nat.bend` reports `126` -- the CLI counts every law body the parser
saw as a `?TODO` in the *whole closure* (`main.ts`'s `book_read` sums
`book.hols + book.open`, and `book.hols` is bumped in the parser, before the
loader's `done` bookkeeping that keeps a filled file out of `book.open`). So a
measurement that needs the *definitions* of a laws-only file has to import a
law-stripped copy of it (`sed` out the `law` blocks; the `def`s are
self-contained).

**The cross product itself** is then assembled the way `Rat.mul_assoc` and
`Rat.add.value` assemble theirs: scale both sides of the equation by
`d2 = Yd*Zd` (the inner sum's own denominator) and use the three value
equations `Rat.mk.value` gives -- `B*d2 == R2*b`, `B1*(Xd*Yd) == R1*b1`,
`B3*(Xd*Zd) == R3*b3`, with `R2 = Rat.num(U2,V2)` the inner sum's difference
pair and `R1, R3` the two products' -- each read at its coordinate level
(`Int.eq.pos`/`Int.eq.neg`). After the substitution both sides are

    b*b1*b3 * [ (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd ]        (left)
    b*b1*b3 * [ P1*Zd + P3*Yd + a1*Q2 + b1*P2 ]          (right)

with `Pi = sub(Ui,Vi)`, `Qi = sub(Vi,Ui)` the truncation pairs of the three
involved pairs, so what is left is the pure Nat identity

    (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd  ==  P1*Zd + P3*Yd + a1*Q2 + b1*P2    (T)

-- the common factor `b*b1*b3` is *not* cancelled: it sits on both sides, and
the identity is multiplied by it. (T) is the distributivity fact at the Nat
level: its two sides differ by `(a1-b1)*(U2-V2) - Zd*(U1'-V1') -
Yd*(U3'-V3')`, which is zero because `U2-V2 = (a2-b2)*Zd + (a3-b3)*Yd`,
`U1'-V1' = (a1-b1)(a2-b2)` and `U3'-V3' = (a1-b1)(a3-b3)`.

**Correction.** The first version of this paragraph claimed (T) is a
`Nat.cross_add` combination of two padded equations it wrote out as

    (a1*P2 + b1*Q2) + (b1*U2 + a1*V2)  ==  (a1*Q2 + b1*P2) + (b1*V2 + a1*U2)
    (P1*Zd + P3*Yd) + (b1*U2 + a1*V2)  ==  (Q1*Zd + Q3*Yd) + (b1*V2 + a1*U2)

-- and that is wrong twice over. `cross_add` consumes *one* padding pair
`(t, t2)`, so two hypotheses only combine if their paddings agree: here the
first carries `b1*U2 + a1*V2` and the second `b1*V2 + a1*U2`, two different
terms (they are the cross sum of the truncation pair in the two orders, and
they agree only when `a1*U2 + b1*V2` does). And the paddings are not the
`b1*U2 + a1*V2` shapes at all: what the value equations actually produce are
the *truncation pairs* `(P2, Q2)`, so every term of the padding and of the
coefficient is a product with `P2` or `Q2`, never with `U2` or `V2`. Written
in the truncation spelling, with `C = Yd*Zd`, `dd = (Xd*Yd)*(Xd*Zd)`,
`bd = b1*b3` and

    A  = a1*P2 + a2*Q2        G1 = a1*P2 + a2*Q2 + b2*P2
    q2 = b1*Q2 + b2*P2        G2 = b2*P2 + b1*Q2 + a2*Q2

(the two summand-groups `cross_add` needs), the padded hypotheses that *do*
combine are

    A*C + q2*X*C           ==  G1*C + G2*X*C          (padding q2*X*C, q2X = q2*X)
    q2*dd + q2*X*C*bd      ==  (q2*X*C)*bd + D2*E2

with `D2*E2 = b1*Q2 + b2*P2`: the first is the positive coordinate reading of
the inner sum's value equation scaled by `X*C`, the second the negative one of
the two products' readings, and `cross_add` at

    (A, A2, B, B2, t, t2) := (A*C, G1*C, q2*dd, D2*E2, q2*X*C*bd, G2*X*C*bd)

gives `A*C + D2*E2 == G1*C + q2*dd`, which is mk.eqv.raw's hypothesis once the
two sides are respelled by `Int.mul_scale` (and the `b*bd` factor is carried
along both sides -- it is never cancelled). Neither hypothesis is a `sub_cross`
instance: `sub_cross` is the *one-coordinate* cross sum of a single inner sum
(what the additive block uses, since there the inner sums are never scaled),
while here the inner sum's value equation is scaled by the two product
denominators and read at both coordinates.

Two statements in this neighbourhood are false as they stand and are recorded
here so that nobody re-derives them:

  - the four-scale `cross_sum` -- `e1 : s3*f3 + s1*f1 == (f1+f3)+f4`,
    `e2 : s4*f4 + s2*f2 == (f2+f4)+f3`, conclusion `T1+T2 == T3+T4`. It is
    false for free scales, and the `s1 = s3`, `s2 = s4` the intended use has
    do not rescue the *statement*: it is the hypothesis set that is too weak,
    not the instantiation that is wrong.
  - `swap` in the shared-*value* form: `u+v == w`, `x+y == w` gives
    `u+y == x+v`. Witness `u=0, v=1, x=1, y=0, w=1`: both hypotheses hold
    (`0+1 == 1`, `1+0 == 1`) and the conclusion asks `0+0 == 1+1`, i.e.
    `0 == 2`. The two hypotheses share a *value*, not a term, and nothing
    forces the pairs to be the same pair.

Nothing in the route needs a new law; what it needs is the shuffle inventory
already in `rat_proofs.bend` (`exch4`, `foldA`/`foldB`, `split`) plus a
Nat-level ring block for the projection-to-truncation identities. Estimated at
the size of `Rat.add_assoc`'s Nat half, i.e. a few hundred lines -- it was not
attempted in this round.

`Rat.mul_add_left` is then free: `(x + y)*z = z*(x + y) = z*x + z*y =
x*z + y*z` is `Rat.mul_comm`, `Rat.mul_distrib`, and two `Rat.mul_comm`s under
a congruence, the same shape `Rat.add_exchange` has on the additive side.

### `Rat.mul_distrib` landed: three comparisons, and (T) needs no case split

Landed, and the last two Rat laws the field needs:

- **`Rat.mul_distrib`** -- `x*(y+z) = x*y + x*z` over the canonical
  presentation, no coprimality hypothesis and no comparison parameter (nothing
  is cased on anywhere in the fill).
- **`Rat.mul_add_left`** -- `(x+y)*z = x*z + y*z`, and the previous round's
  prediction held exactly: `mul_comm`, `mul_distrib`, one congruence per
  summand, three steps and no arithmetic. It was written after `mul_distrib`
  landed and checked on its first run, so the "free" claim is now a measurement
  rather than an expectation.

Cost: `rat_proofs.bend` 2665 -> 3469 lines -- fourteen proof-only helpers
(`R.Rat.nat.swap`, `add2`, `scale.eq`, `scale.eq.r`, `gather`, `distrib`,
`pair.scale`, `cross1`, `dist4`, `align.zd`, `align.yd`, `tl.scaled`,
`tr.scaled`, `cross2`; 554 lines with their comments) plus the 208-line
`mul_distrib` fill and the 42-line `mul_add_left` fill; `rat.bend`
945 -> 1023 (the two laws and their comments). All five gates green,
`rat.bend` alone reports **197** TODOs (was 195, one per new law).

#### The design fix: three `mk.eqv.val` comparisons, not one

The previous round settled the *consumer* (`mk.eqv.val`, not `mk.eqv.raw`)
but left one step unmeasured -- "spilling `numof(M2)`, a `div`/`gcd` term,
into the inner sum's own value pair inside the cross sum" -- and that step is
where the route looks hard. It is hard, and it does not have to be taken:
comparing the two sides **directly** puts every quotient of both operations
into *one* cross sum, which then needs the whole equation multiplied by
`K = d1*d2*d3`, the six value equations substituted inside it, and `K`
cancelled at the end (`Nat.mul_right_cancel`) -- the substitution is real
work and it is bookkeeping for a single comparison.

Comparing in three hops removes all of it, because each hop is at its own
denominators:

    mk(num(x)*numof(M2), xd*denof(M2))
      == U_L = mk(num(x)*Rat.num(U2,V2), Xd*d2)        [the inner sum's value]
      == U_R = mk(P1*d3 + P3*d1, Q1*d3 + Q3*d1 over d1*d3)
      == Rat.add(M1, M3)                               [Rat.add.value, exactly]

- the first hop needs only the **two coordinates of `Rat.mk.value` at the
  inner sum**, scaled by `Xd` -- i.e. exactly the `Rat.value.scaled.pos`/`.neg`
  pair the previous round landed, used for the first time here;
- the second hop is `(T)` multiplied by `d1*d3` and nothing else -- no value
  equation, no `div`, no `gcd`;
- the third hop is `Rat.add.value`: `U_R` *is* that law's own conclusion, so
  this step is two `Rat.mk.rep` rewrites (backwards), two `pos_witness`
  rewrites to the successor denominators `Rat.add.value` is stated over, the
  law, and `Int.mul_scale` on the sum's two products. No cross sum at all.

That is the general lesson for the remaining Rat work: an identity that can be
decomposed through the *value* of an intermediate result should be, because
each hop is then a comparison the existing laws already state, and the one
hard Nat identity stays small.

#### (T) from the padded hypotheses -- the letters the previous round got wrong

`R.Rat.nat.distrib` proves

    (a1*P2 + b1*Q2) + Q1*Zd + Q3*Yd  ==  P1*Zd + P3*Yd + a1*Q2 + b1*P2

with **no case analysis**. The route one reaches for first -- split on the sign
of `x`'s numerator, where the identity collapses to the inner sum's cross sum
scaled by `a1` (in the `b1 = 0` branch) or by `b1` (in the `a1 = 0` branch) --
is not needed: the identity is uniform in the two coordinate pairs, and what
proves it is the padded-hypotheses idea this file's earlier paragraph described
with the wrong letters:

    e1 : a1*P2 + b1*Q2   + (a1*V2 + b1*U2) == a1*Q2 + b1*P2   + (a1*U2 + b1*V2)
    e2 : (P1*Zd + P3*Yd) + (V1*Zd + V3*Yd) == (Q1*Zd + Q3*Yd) + (U1*Zd + U3*Yd)

Both carry the padding `(V1*Zd + V3*Yd, U1*Zd + U3*Yd)`, and `Nat.cross_add`
at `(A, A2, B, B2, t, t2) := (a1*P2 + b1*Q2, a1*Q2 + b1*P2, P1*Zd + P3*Yd,
Q1*Zd + Q3*Yd, V1*Zd + V3*Yd, U1*Zd + U3*Yd)` gives the goal after one
re-association. Where the two facts come from:

- `e1` is the inner sum's cross sum `P2 + V2 = Q2 + U2` scaled by `a1` and by
  `b1` and added (`R.Rat.nat.scale.eq` twice, then `R.Rat.nat.add2`, whose
  `swap` shuffle is the five-step association `(A+B)+(t+s) -> (A+t)+(B+s)`);
  no truncation reasoning, so both scales are the *raw* coordinates.
- `e2` is the same two-step construction on the two product pairs, scaled by
  the other summand's denominator `Zd` and `Yd`.
- The padding equality is where the two `R.Rat.nat.gather` facts enter: they
  are the pure ring facts

      a1*U2 + b1*V2 = U1*Zd + U3*Yd        a1*V2 + b1*U2 = V1*Zd + V3*Yd

  i.e. distributing each multiplier over the inner pair's coordinates and
  folding the products back into the product pairs' coordinates -- which is
  also the sentence the whole identity *means*: `(a1-b1)(P2-Q2) =
  Zd(P1-Q1) + Yd(P3-Q3)`.

The previous round's restatement of `e1`/`e2` was wrong in the way this file
recorded (its paddings were `b1*U2 + a1*V2` shapes, which are also swapped
between the two hypotheses and so cannot both match `cross_add`'s single
padding pair); the two written above do combine, and the fact that makes them
combine is that the inner sum is scaled by `a1` on one side of `e1` and by
`b1` on the other, so the *shared* piece is the pair `(V1*Zd + V3*Yd,
U1*Zd + U3*Yd)` and not a middle summand.

The two hops that do not feed `(T)` are ring bookkeeping with no arithmetic
content, and they are the bulk of the helper block:

- `R.Rat.nat.cross1` + `pair.scale`: the first hop's cross sum, four products
  re-associated from the shape `(c1*x1 + c2*x2)*(d2*Xd)` to
  `(c1*y1 + c2*y2)*(Xd*m2)` -- one commutation each because the left side's
  own denominator is `Xd*m2` (written by `Rat.mul`) while the scaled value
  equations come out of `Rat.value.scaled` in the `m2*Xd` order;
- `R.Rat.nat.cross2` + `tl.scaled`/`tr.scaled`/`dist4`/`align.zd`/`align.yd`:
  the second hop, `(T)` multiplied by `d1*d3` and re-associated into
  `ULp*(d1*d3) + URn*(d2*Xd) = URp*(d2*Xd) + ULn*(d1*d3)`. Every alignment is
  a commutation of the multiset `{Xd, Yd, Zd}` with its multiplicities -- four
  or five steps each, and pure `mul_comm`/`mul_assoc` after that.

Nothing in the block needs a new Nat law: three `Nat.sub_cross` instances, one
`Nat.cross_add`, and `mul_comm`/`mul_assoc`/`mul_add_left`/`mul_distrib`.

#### Four checker rules this round paid for

- **`%`'s semantics, exactly.** `%E : {P}` takes the *current* goal `T`, solves
  `P`'s hole against `T`, and rewrites the occurrence the hole marks -- which
  must therefore be an occurrence of `E`'s **right** side -- into `E`'s left
  side; the rest of the chain then proves the rewritten goal. So the annotation
  is the goal *before* the step, not after, and it must place the hole at the
  exact subterm being rewritten: **there is no automatic congruence.** An
  annotation whose hole sits at a larger term (`{Nat.mul(x, Nat.mul(Yd, _))}`
  when only `mul(Xd,Zd)` inside it is being rewritten) demands an evidence
  about that larger term and fails. The rule is now measured rather than
  guessed, and the two alignment helpers are written with it.
- **A let-bound `Equal.cong` cannot be inferred** -- the earlier note is
  confirmed, with the exact symptom: `+u3s = Equal.cong(Nat, I.Int, v =>
  I.Int{v, 0n}, ds3, d3, e3s)` fails with `expected : an annotated term
  (cannot infer)` and `observed : int.Int{...}` (the *substituted* argument),
  which reads like a problem with the constructor literal and is not one; the
  same cong inlined in a `Equal.trans` checks. Let-bound `Equal.trans` values
  are fine, and so are let-bound *applications* of helper defs.
- **A hypothesis can be made reusable with `+`.** `R.Rat.nat.distrib` needs
  the same cross sum twice (once per scale), and the default linear hypothesis
  gives `expected : e2 / observed : e2 (consumed more than once)`. `+e2: {...}`
  in the telescope fixes it, which is the same quantity discipline the laws
  use on their own fields.
- **Constructor literals in argument positions**: `I.Int{ds, 0n}` as the `a`
  or `b` argument of a `cong` goes through `I.Int.unit(ds)` in this codebase's
  idiom; the failure above was *not* this, but the units are what the landed
  fills spell and there is no reason to write the literal.

Next, on the same recipe: **QExt over Rat** -- the field axioms, then the
multiplicative inverse `1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)`, whose
denominator is a difference of two squares and so is the first place the two
distributive laws meet a `Rat.sub`.


## Cross-file imports: the helper-naming rule that cost three rounds

`import ./laws.bend as L` plus `import ./proofs.bend` from a third file **does
work** -- that is the nat/int/qext pattern in "Laws vs proofs" above, and it is
how `int_proofs.bend` uses proved `Nat` laws. When it appears not to work, the
cause is almost always the naming rule below, not the split itself.

**The rule.** In a proofs file, two kinds of `def` share one namespace:

- a **fill** of a law must be spelled `def <laws-alias>.<law key>(...)` --
  that prefix is the mechanism that attaches the proof to the law;
- a **proof-only helper** must be named **bare** (`Nat.pred`, `NatIsPos`,
  `Nat.succ_add_ne_zero`), never with the laws-file alias.

A helper that carries the alias resolves only while the proofs file itself is
the *main* file. The moment another file imports it, the internal reference
becomes

    Error:
    - expected : a defined name
    - observed : R.Rat.add.piece

which reads as "this file cannot be imported" and is not.

**What it cost here.** All three of `Int.canon`-adjacent rounds were fine, but
`rat_proofs.bend` had **35 helpers** named with the alias (`R.Rat.add.piece`,
`R.Rat.add.cross`, `R.Rat.nat.d3`, ...). The symptom above was measured
faithfully and then generalised into "a `*_proofs.bend` file is not importable
at all", which is false. That mis-diagnosis produced `src/qrat_rat.bend` -- a
684-line transcription of `rat.bend`'s statements -- plus the ported fills for
them in `qrat_proofs.bend`, i.e. a hand-maintained duplicate of the whole Rat
layer whose copies nothing mechanically checked.

Commit `c921dbf` renamed the 35 helpers bare. `rat_proofs.bend` still checks,
and a probe that imports `rat.bend` **and** `rat_proofs.bend` and calls
`R.Rat.add_comm` checks too (it failed with exactly the error above before the
rename). The duplicate is therefore unnecessary and **it is gone**: `src/qrat_rat.bend`
(684 lines) is deleted, `qrat_proofs.bend` keeps only the QExt-specific fills
(the two coordinate witnesses, the two `QExt.mul` coordinate chains, and the
four law fills) and calls rat.bend's laws as `R.Rat.<law>`, filled by its
`rat_proofs.bend` import -- 1929 lines to 181. The whole QExt layer above the
Rat one now costs one call per Rat law: `QExt.neg_neg`, which used to carry a
port of `Rat.neg_neg` plus the Nat helper `nat.sub.min` and the two Rat helpers
`rat.mk.fixed.neg`/`rat.neg.neg`, is two `R.Rat.neg_neg` applications at the
law's own telescope (a literal `Nat.cmp` and `{==}` evidence, exactly as
`rat_proofs.bend` passes them to its own inner `mk.fixed`). So: **no layer of
this project needs to restate another layer's laws and proofs.**

**The mechanical check**, before concluding that anything is unimportable:

    # any def in the proofs file whose name is not a law key in the laws file
    # is a helper, and must be bare
    comm -23 <(grep -o '^def <alias>\.[A-Za-z0-9_.]*' proofs.bend | sed 's/^def <alias>\.//' | sort) \
             <(grep -o '^law [A-Za-z0-9_.]*' laws.bend | sed 's/^law //' | sort)

Every line it prints is a helper to rename. Empty output means the rule is
satisfied.

**Import order**: the round that deleted the duplicate tested it, and it is
*not* load-bearing here. `qrat_proofs.bend` lists the laws files first
(`nat.bend`, `int.bend`, `rat.bend`, `qrat.bend`) and the proofs files after
(`nat_proofs.bend`, `int_proofs.bend`, `rat_proofs.bend`), which is the order
`int_proofs.bend` uses; a copy of the same file with `rat_proofs.bend` imported
**first**, before `rat.bend`, checks just as green (`All terms check.`). So both
orders work at this size, and the laws-first order is kept as the convention
rather than as a rule.

**The lesson worth keeping.** A symptom that is measured honestly can still be
generalised wrongly. When a wall appears, compare it against the mechanism this
document already describes -- the helper-naming rule was written down for
`nat_proofs` long before it bit `rat_proofs`.

## The composing QExt laws: what the canonical presentation buys, what blocks the general form

`QExt.add_assoc` landed in the *canonical presentation* -- six coordinates, each
`Rat{Rat.num(np,nn), 1n+dp}` -- and its fill is exactly what the componentwise
shape promised: one `R.Rat.add_assoc` per coordinate, two calls, no hypothesis
and no case analysis. That is the same convention `QExt.neg_neg` already uses and
the one qrat.bend's header documents, and it is what makes the call possible at
all: `Rat.add_assoc`'s nine parameters *are* that presentation.

**The form over arbitrary QExt values is not in, and the reason is a proof-side
wall, not a false statement.** Both halves of that claim were measured.

*Truth side: nine witnesses, no counterexample.* Law-level reasoning is not
available here (the checker cannot reduce `Rat.add` on a variable), so the law
was **evaluated**: the operations were called on witnesses outside the canonical
presentation -- zero denominators, non-successor denominators, two-sided and
gcd-reducible numerators -- and the two sides compared. Writing
`Rat{Int{p,q}, d}` for `(p - q)/d`, all nine triples agree:

    (1/0, 1/1, 1/1)         both Rat{Int{1,0}, 0}
    (1/1, 1/0, 1/0)         both Rat{Int{0,0}, 0}
    (9/4, 2/6, 7/0)         both Rat{Int{1,0}, 0}
    (0/0, 3-1/2, 1-1/0)     both Rat{Int{0,0}, 0}
    (3-1/2, 1/3, -2/5)      both Rat{Int{14,0}, 15}
    (7-2/4, 1-5/6, 3-3/2)   both Rat{Int{7,0}, 12}
    (2-1/0, -3/0, 5/0)      both Rat{Int{0,0}, 0}
    (2-3/0, 5-1/0, -4/0)    both Rat{Int{0,0}, 0}
    (4/6, -5/0, 2-2/2)      both Rat{Int{0,1}, 0}

The pattern behind them is that a zero denominator makes both sides collapse to
the *sign* of one coordinate (the gcd of the inner sum's magnitude with a zero
denominator is that magnitude, so `div` turns the numerator into +-1 and the
outer denominator into 0), and the two sides collapse with the same sign. So no
evaluated witness justifies a hypothesis.

*Proof side: the closing lemma needs positivity, which nothing can supply.* For
arbitrary coordinates the Rat-level goal's two sides are `mk`-headed terms, and
the only lemma that compares two such terms is `Rat.mk.eqv.val`, whose
hypotheses include `Nat.cmp(0n, d1) == LT{}` and `Nat.cmp(0n, d2) == LT{}` --
positivity of the two denominators it compares. An arbitrary `Rat` has none:
`Rat{Int{1,0}, 0}` is a legal argument, `mk`'s behaviour there is junk (rat.bend
says so where it defines `mk.go`), and every value lemma in the layer carries the
same hypothesis for the same reason (`mk.value`, `mk_idem.raw`,
`add.value.mixed`, and `Nat.div_pos_wit` under them). Reaching the general form
therefore needs one of:

- an mk-headed `Rat.add_assoc` stated at those same hypotheses -- and then a way
  to *discharge* them for arbitrary coordinates, which does not exist (an
  arbitrary coordinate's denominator is not positive, and no bridge turns an
  arbitrary `Rat` into a canonical one: `==` is structural, so
  `Rat{Int{4,0}, 2}` is not `Rat{Rat.num(4,0), 2}`); or
- a proof of the zero-denominator cases on their own: a case analysis on which of
  the three input denominators is zero, with the collapse lemmas under it
  (`gcd(a, 0) = a`, `div(a, a) = 1`, `mul(x, 0) = 0`, `div(0, g) = 0`), which the
  nine witnesses above say would work but which is a campaign of its own.

**The multiplicative composing laws are further out, for a second reason.**
`QExt.mul`'s coordinates are *sums of products* (`xa*ya + d*xb*yb`), so
`QExt.mul_assoc` and `QExt.mul_distrib` are not componentwise
`Rat.mul_assoc`/`Rat.mul_distrib` calls at all -- the derivation needs those Rat
laws at **mk-headed** arguments (every product and every sum in the goal is an
operation's output), i.e. the same rung-2 work, and it needs it for three Rat
laws rather than one.

**The rung-2 shape, when it is built.** The statement that both a fill and a
caller can use is over *arbitrary Rat variables*
(`for +x: Rat, +y: Rat, +z: Rat {add(add(x,y),z) == add(x,add(y,z)) : Rat}`), not
over `Rat.mk(...)` applications: a caller's coordinates are pattern variables,
`Rat.add` on a variable is stuck, and a law whose arguments are constructor
literals cannot be instantiated at a stuck term. Its fill is reachable in the
same way the fills in this repo already reach past a match -- one helper def per
level of destructuring, since a def's *parameters* may be matched at its body
head (`match xa ya za:` inside the helper that takes them), which sidesteps the
"no nested matches on pattern variables" rule without weakening anything.

## The rung-2 mk-headed `Rat.add_assoc`: the one bridge, and why the `Int` endpoint cannot carry it

The rung-2 additive law over arbitrary Rat variables with the positivity of the
three inputs as hypotheses (`{Nat.cmp(0n, Rat.denof(x)) == LT{}}` on `x`, `y`,
`z`) is settled except for **one bridge**: "mk of a projection pair is mk of
`Rat.num(a,b)`". Everything else about it was derived and nothing about it is a
fill problem; the bridge is where the round stopped, and the three measurements
below are why it is not the step it looks like.

**What the bridge's left side actually is.** `Rat.mk_idem.raw`'s left side is
`mk(Rat.numof(M), denof(M))` with `M = mk(Rat.num(a,b), d)`, and `mk` reduced its
argument, so it is

    mk(I.Int{Nat.div(Nat.sub(P, Q), G2), Nat.div(Nat.sub(Q, P), G2)}, W)
    P = sub(a,b)   Q = sub(b,a)   G2 = gcd(sub(P,Q) + sub(Q,P), d)   W = denof(M)

-- note the *outer* gcd: its magnitude is `mag(P,Q)`, a sum of two truncations,
not `mag(a,b)`. Naming `Rat.num(a,b)` means two **`sub_diag` collapses that reach
under a `Nat.div` dividend**, one per coordinate, and the two sit in *different
positions of the same `Int`*.

**Why one congruence cannot do both.** `Equal.cong(Nat, Int, u => Int{div(u,G2),
r}, sub(P,Q), P, sub_diag(...))` puts `P` in the first coordinate and leaves the
second untouched, so the second coordinate's own collapse is unreachable by the
same motive; a 2-step `Equal.trans` using two such congs then leaves

    Nat.div(Nat.sub(Nat.sub(a,b), Nat.sub(b,a)), G) == Nat.div(Nat.sub(a,b), G)

which **`{==}` cannot close** although `sub_diag` proves the two dividends equal:
once one coordinate of an `Int` has been rewritten, the two `Int`-level endpoints
stop being convertible, so the checker no longer sees the pair it would have to
compare. (A let-bound `u => Nat.div(u, G2)` cong is rejected outright --
`cannot infer` -- the rule this file already records.)

**The measurement that retires the "bridge" framing.** `R.Rat.num(p,q)` and
`I.Int{p,q}` **are definitionally equal** -- `Rat.num` unfolds to
`Int{sub(p,q), sub(q,p)}` -- so there is no gap of *that* kind to bridge anywhere.
The difficulty is only the truncations inside the projection's two `div`s, and
that is why the honest statement of the missing fact is
`mk(Int{div(P',G2), div(Q',G2)}, W) == mk(Rat.num(a,b), W)` with `P'`, `Q'` the
projection's own arguments, not a respelling of `Rat.num`.

**Consequence for the statement.** `mk(I.Int{p,q}, W) == mk(Rat.num(p,q), d)` is
**false as a universal statement**: it would demand
`Int{p,q} == Rat.numof(mk(Rat.num(p,q),d))`, i.e. that the projection's two
quotients reproduce the raw pair. So the helper has to be **parameterized by the
truncation equalities** and both collapses have to be performed in **one pass**
(a single `Equal.cong` whose evidence is the pair equation, not two steps).

**Last measured error, for the record:**

    - expected : Nat.sub(a, b)
    - observed : Nat.sub(Nat.sub(a, b), Nat.sub(b, a))
    Location: Rat.mk_idem.form

**The one spelling this round did not try**, and the reason it is the right next
move: state the helper over
`mk(I.Int{sub(sub(a,b),sub(b,a)), sub(sub(b,a),sub(a,b))}, W)` on the left --
exactly the pair `mk_idem.raw` produces, written as one term -- and reach the
goal's `mk(Rat.num(a,b), W)` by **one `Equal.cong` on `Rat.mk`'s second argument
plus the two coordinate collapses in one pass**, so that no `Int`-level endpoint
is ever left half-rewritten. The alternative, if that fails too, is to have the
worker supply positivity at the projections' own `Rat.denof` spelling (`pq`),
which `mk_idem.raw` requires but which no caller can currently write
definitionally.

### The bridge, attempted: the coordinates do not reduce, and the reducer is `Nat.sub` (measured)

The spelling above **was** tried, and the attempt turned the three guessed facts
below into measurements. The helper was written out in full, in five variants, in
`rat_proofs.bend`; each one failed at the same place, and the tree was restored.

- **`Nat.div(sub(sub(a,b),sub(b,a)), G2)` does not reduce to `Nat.div(sub(a,b), G2)`**,
  and neither do the two `Nat.sub` terms alone. `Nat.sub` matches on **both**
  arguments (`base.bend`: four cases, `0n 0n` onwards), so a diagonal
  `sub(sub(X,Y), sub(Y,X))` is stuck: nothing about it is a constructor, and the
  comparison that would collapse it lives in `sub_diag`'s *fill*, not in the
  evaluator. Measured directly: the goal `{sub(sub(sub(a,b),sub(b,a)), ...) == sub(sub(a,b),sub(b,a))}` is
  `All terms check.` (that is `sub_diag`'s own statement), while
  `{Nat.div(sub(sub(a,b),sub(b,a)), G2) == Nat.div(sub(a,b), G2)}` is **not**,
  with `{==}`. So "the collapse is definitional under the division" -- the
  assumption the round above was built on -- is **false**, and the two collapses
  are genuinely needed as rewrites.

- **`sub_diag` is only half an answer, and that is a statement and not a fill
  problem.** It gives `sub(sub(X,Y),sub(Y,X)) == sub(X,Y)`; the cross sum
  `mk.eqv.val` asks for needs `sub(X,Y) == sub(sub(X,Y),sub(Y,X))` -- the same
  equation read the other way -- and `Equal.sym` is the only thing that turns one
  into the other. `sub_diag` in that orientation is rejected, and `Equal.sym`
  around it is rejected too, with the two ends of the error **swapped**:

      - expected : {sub(sub(b,a),sub(a,b)) == sub(b,a)}
      - observed : {sub(sub(sub(b,a),sub(a,b)), sub(sub(a,b),sub(b,a))) == sub(sub(b,a),sub(a,b))}

  Swapping `Equal.sym`'s arguments, and swapping the `Equal.cong`'s `(a, b)`
  pair, each only swap the same two messages: every one of the four combinations
  was run, and in each the demand and the evidence come back as each other's
  reverse. So at this argument shape **`Equal.sym` cannot be composed with
  `Equal.cong`**, whichever way round it is written -- a new checker entry for
  this file's list, and the reason the "one pass" plan above cannot be assembled
  the obvious way. (What *does* work at these shapes: a **named def** as the
  congruence motive. `u => Nat.mul(u, W)` is rejected where
  `def Rat.mul.W(+W, u) = Nat.mul(u, W)` checks, and
  `u => Nat.add(A, u)` is rejected where a named `Rat.add.L`/`Rat.add.R` checks --
  both measured, both at the real argument shapes.)

- **The cross sum needs the *first* coordinate stated non-collapsed**, which is
  why `mk.rep` cannot be the closing step either. `mk.eqv.val` instantiates
  `xp := div(sub(P,Q), G2)`, and the first coordinate of a *quotient* has no
  collapse (`div(Pq, G2)` is not `div(sub(P,Q), G2)`), so the cross sum's left
  side is stuck with `Pq` and the right with both raw coordinates. The only
  product identity that then closes it is `sub_cross`'s cross sum
  (`(a-b) + b == (b-a) + a`) at the raw pair, lifted through `mul_add_left` on
  both sides and `add_comm` -- and that lift is exactly where the `sub_diag`
  orientation above bites.

**State of the rung-2 law after this round.** The mathematics is settled: the
cross sum is `Nat.sub_cross` at `(sub(a,b), sub(b,a))`, the two product spellings
are two `Nat.mul_add_left`s, and the closing is `Rat.mk.eqv.val` + `Rat.mk.trunc`
-- all four verified in isolation (`All terms check.`). What is missing is one
composition: a `Equal.cong` whose evidence is a `sub_diag` used in the reverse of
its stated orientation. The two ways out that the measurements leave open are (a)
a `sub_diag`-shaped law **stated in the reverse orientation** (which is legal and
would make the evidence direct -- no `Equal.sym` anywhere), and (b) a cross-sum
law stated over the collapse so that no re-orientation is needed at all.

## The reverse law landed -- and what the write path actually costs (measured)

Way (a) above was taken. `nat.bend` has `sub_diag_rev` (`sub(np,nn) ==
sub(sub(np,nn), sub(nn,np))`, the twin spelling of `add_assoc_rev` /
`cmp_gt_of_lt` / `mul_add_left`), its fill in `nat_proofs.bend` is one
`Equal.sym` around `sub_diag`, and both check. Counts move transitively as the
README records: nat 126 -> 127, rat 197 -> 198, qrat 202 -> 203. **The law is
correct, filled and green; it does not by itself close the rung-2 fill.** The
round stopped at a *different* wall, and the three measurements below are what
the next round should start from.

**`Equal.cong`'s orientation, read off the source, is a rule worth writing
down.** `Equal.cong(A, B, f, a, b, e)` is defined as `%e : {f(a) == f(_) : B}`
and `Equal.sym(A, a, b, e)` as `%e : {_ == a : A}`, i.e.

    e : a == b      |- cong f a b e : f(a) == f(b)
    e : a == b      |- sym a b e   : b == a

At the shapes this file uses that is exactly what the checker does: the call
`cong(Nat, Int, u => Int{u, c}, sub(X,Y), sub(sub(X,Y),sub(Y,X)), sub_diag_rev)`
synthesizes `Int{sub(X,Y),c} == Int{sub(sub(X,Y),sub(Y,X)),c}` -- the collapsed
side first, the diagonal side second -- and `sym` around the same evidence
yields the reverse. So a rewrite in the orientation "collapsed -> diagonal"
takes `sub_diag_rev` and one in the orientation "diagonal -> collapsed" takes
`sub_diag` through `sym`; the spelling is what makes the evidence direct, and
that part of the round's premise is confirmed.

**A `cong` **nested** inside another `cong` does not compose at this shape, and
the two message pairs are the reverse of each other.** Every one of the four
combinations of `(inner a, inner b)` with `(plain evidence, Equal.sym around
it)` was run at the product-collapse goal
`Int{Xp,Yp} == Int{sub(X,Y),sub(Y,X)}` (`Xp = sub(sub(X,Y),sub(Y,X))`,
`Yp = sub(sub(Y,X),sub(X,Y))`, under the motive `u => Int{u, 0n}`):

    expected : {sub(X,Y) == Xp}          observed : {Xp == sub(X,Y)}
    -- and the reverse pair for each of the other three spellings.

The outer `cong` wants `f(a) == f(b)` at its own endpoints; the inner one
delivers `f(a') == f(b')` at whatever its own endpoints are, and no choice of
the four spellings makes the two meet. This is the same "the demand and the
evidence come back as each other's reverse" shape the section above records for
`Equal.sym`, now one level down: **the congruence has to be *standalone* (a
direct argument of `Equal.trans`) for the orientation rule to apply.** Three
rewrites of this kind are therefore written as
`trans(a, b, c, cong(...), cong(...))` with the intermediate type spelled out --
which is the repo's own idiom, and the measurement says it is the only one.

**The wall is now `Int.mul`, not the evidence.** With the two standalone congs
in place the chain reaches

    Int.mul(Int{Xp, Yp}, Int{d, 0n})  ==  Int{mul(sub(X,Y), d), 0n}

and the remaining step is `Int.mul_scale` at `(sub(X,Y), Yp)`, whose own fill
(`int_proofs.bend:154`) proves that product reduces in exactly that way. What the
checker reports instead is a *reduction* mismatch: the goal's left side comes
back **stuck** as `Int.mul(...)` while the very same term inside the `trans`
argument is observed **unfolded** to
`Int{add(mul(Xp,d), mul(Yp,0)), add(mul(Xp,0), mul(Yp,d))}`:

    - expected : {Int.mul(Int{Xp,Yp}, Int{d,0n}) == Int{mul(sub(X,Y),d), mul(Yp,0n)} : Int}
    - observed : {Int{add(mul(Xp,d), mul(Yp,0n)), add(mul(Xp,0), mul(Yp,d))} == ...}

So the same application is unfolding on one side of the comparison and staying
stuck on the other. Two routes are open and neither was run to ground: force the
unfold once, at `Int` level, so that both sides are the same *term* rather than a
term and its reduct (the repo already has the shape -- `Rat.add.value`'s fill
writes `Int.mul_scale` as the first `trans` step and never relies on the goal
reducing); or state the collapse helper over the *unfolded* pair
(`Int{add(mul(...),mul(...,0n)), ...}`), which is `I.Int.mul_scale`'s own source
spelling, so that the motive never has to see `Int.mul` at all. The second is
the smaller change and is the one to try first.

**Not run, and therefore not claimed:** the rung-2 `Rat.add_assoc` statement is
not in `rat.bend`, `QExt.mul_assoc` / `QExt.mul_distrib` / the multiplicative
inverse are not started, and `QExt.add_assoc` is still the canonical-presentation
form. Nothing was left stated-but-unfilled: `scratch.bend` was restored to its
committed state and all six gates are green at that commit.

## The rung-2 additive law landed, and the bridge was not needed (measured)

`Rat.add_assoc.arb` is in `rat.bend` and filled in `rat_proofs.bend`: arbitrary
`Rat` variables `x`, `y`, `z` with `{Nat.cmp(0n, Rat.denof(_)) == LT{}}` on each
of the three, conclusion `add(add(x,y),z) == add(x,add(y,z))`. Counts move as the
README records: rat 198 -> 199, qrat 203 -> 204 (the canonical `Rat.add_assoc`
stays *stated*, so no existing call site moved; its fill is now one call of the
general law -- see the ordering rule at the end of this section).

**The route that worked is not the route the last two rounds were on.** Those
rounds tried to reach the law by *bridging a mk-headed summand*: to turn
`mk(numof(M), denof(M))` into `mk(Rat.num(a,b), W)` (`Rat.mk_idem` and its five
attempted forms), which is where the `Int.mul` wall and the nested-`cong` wall
were measured. The fill that landed never writes those terms: it destructures the
three inputs **twice** -- once into the Rat fields, once into the three `Int`
numerators -- and after that second level *every* term on both sides is a
constructor-headed `mk` whose arguments reduce by themselves. No `mk_idem`, no
projection bridge, no `Int.mul`-stuck-against-its-reduct comparison appears
anywhere in it. The two measurements that stopped the previous round are still
true statements about the terms *that route* produces; they are simply not on
this one. (The three `*_proofs` gates and `scratch` are green at this commit, and
`rat_proofs.bend` has no unfilled law.)

**Why two levels, and why the two matches are helpers.** `Rat.add(x, y)` on a
*variable* is stuck -- `Rat.add` destructures its arguments -- so the first match
(Rats into fields) is what makes the operations reducible at all. After it the
numerator of each input is still an `Int` *variable*, so `Int.mul(numerator, unit
den)` is stuck in turn (`Int.mul` matches on its first argument), and the `mk`
around the stuck sum cannot destructure its argument. The second match (the three
`Int`s into their coordinate pairs) is what makes all of that reduce. Each level
is a `def` whose *parameters* are matched at its body head, which is the repo's
way around "no nested match on a pattern variable"; the level-2 helper's
statement is the law's own conclusion written over the three `Int` numerators,
and the coordinates cannot appear in a type (they are bound by the match inside).

**A dependent match does refine the hypotheses, measured.** The law's positivity
hypotheses are stated over `Rat.denof(x)`; in the level-1 branch `px` is usable at
`{Nat.cmp(0n, xd) == LT{}}` (the checker rewrites `Rat.denof(Rat{xn,xd})` to
`xd`), so the hypotheses pass straight into the level-2 helper. A two-line probe
(a helper taking `{Nat.cmp(0n, d) == LT{}}` called with `xd` and `px`) checks,
and that is what the fill relies on.

**The chain is the old canonical chain, at raw coordinates -- and it is now the
only copy.** The three
inputs' numerators are the pairs the match bound -- *truncations of nothing*, the
whole difference from rung 1 -- the inner sums' clean coordinates are the two
`Int.mul_scale` re-spellings `U1/V1`, `U2/V2`, the mk-headed summands become
`mk(Rat.num(P,Q), d)` by `Rat.mk.trunc`, each outer add is one
`Rat.add.value.mixed`, and the closing is `Rat.mk.eqv.val` at
`Rat.nat.cross4`'s cross sum from the two `Nat.sub_cross` instances. That whole
Nat block is *verbatim* what the canonical fill had: its hypotheses are gaps in
the raw coordinates, so it never saw the presentation at all. `R.Rat.add_assoc`
(the canonical law's fill) is now one call of this one --
`Rat.add_assoc.arb(Rat{Rat.num(np1,nn1), 1n+dp1}, ..., {==}, {==}, {==})` -- since
at `Rat{Rat.num(np,nn), 1n+dp}` each hypothesis is `Nat.cmp(0n, 1n+dp)` up to the
definition of `Rat.denof`, i.e. `LT{}` by computation. The 227-line canonical
chain is gone; the general fill carries it.

**One ordering rule this cost, measured.** The wrapper's *first* spelling put the
canonical fill before the general one in the file, and the checker rejected it
with

    - expected : a filled definition (an unfilled law is a dead claim: live code
                 cannot use it)
    - observed : rat.Rat.add_assoc.arb

-- a *law* may only be used in live code once its fill has been processed, and
fills are processed in file order. Moving `R.Rat.add_assoc.arb`'s definition
above the wrapper's fixed it with no other change. So in a proofs file that
wraps one law with another, the wrapped law's fill has to come first.

**Two pieces had to be new, and both are general.**

- `Rat.add.value.mixed` (same key, statement generalized): its second summand was
  `Rat{Rat.num(np2,nn2), 1+dp2}`, and rung 2 has `Rat{Int{Zp,Zn}, D}` -- a *raw*
  pair, which is a different pair from `Rat.num(Zp,Zn)` unless a coordinate is
  zero, over a denominator that is carried rather than computed. The old
  statement is the reading `Zp := sub(np2,nn2)`, `Zn := sub(nn2,np2)`,
  `D := 1n+dp2` of the new one (since `Rat.num(np2,nn2)` *is*
  `Int{sub(np2,nn2),sub(nn2,np2)}`), which is why the canonical fill's two call
  sites only gained three arguments. `D`'s positivity is a third hypothesis of
  the same kind as the two it already had. The fill did not change its shape at
  all: `Rat.add.mixed.cross` was already stated over an `Int` numerator and a
  `Nat` denominator.
- `Rat.div.pos` (a bare proof-only helper, no new Nat law): the positivity of
  `Rat.denof(mk(Rat.num(P,Q), d)) = div(d, G)` at the *dividend's own spelling*.
  `Nat.div_pos_wit` is stated at `div(1+ap, G)`, and here `d` is a variable
  product (`Xd*Yd`), so no `1+ap` reduces to it -- which is exactly why
  `Rat.mk_idem.raw` and `Rat.add.value.mixed` take the fact as a hypothesis and
  why the earlier rounds called the derivation unavailable. It is available, by
  two rewrites: `pos_witness` turns `d` into `1 + (d-1)`, the *witness type*
  `Nat.divides(G, d)` is transported to `Nat.divides(G, 1+(d-1))` (**the `%`
  rewrite form, `%e : {P(_)}; body`** -- the witness type is indexed by the
  dividend and no conversion re-spells it), and the conclusion comes back along
  the same equation. The helper is stated over `{Nat.cmp(0n, d) == LT{}}` and a
  witness, so any caller with a carried denominator can use it.

**A measurement about `%` worth keeping.** `%e : {T}; body` is a *goal rewriting*
step, not an assertion: the motive `T` has `_` as its endpoint binder, the check
is `T(b) <= goal` (where `b` is `e`'s second endpoint) and the body is checked
against `T(a)` with the trivial equation. That is the only mechanism in the
language that re-spells a *type* -- `Equal.cong`/`Equal.sym`/`Equal.trans` build
equations between terms, and conversion is not a transport -- and it is what
`Rat.div.pos` uses. `Equal.cong`/`Equal.sym` are themselves written with it
(`base.bend`), which is also why the cong-orientation rule the section above
records holds.

**Not done, and therefore not claimed:** `QExt.mul_assoc` and `QExt.mul_distrib`
are not started, and the inverse is not started. The multiplicative laws need
`Rat.mul_assoc`/`Rat.mul_distrib` at mk-headed arguments, i.e. the same two-level
treatment. The first of those is now available (see the section at the end of
this file, which also corrects this paragraph's earlier claim that "no new value
lemma is needed"). The second is not, and *that* is the concrete next blocker,
measured by reading the statements rather than by running anything: `Rat.mul_distrib`
and `Rat.mul_add_left` are stated over `Rat{Rat.num(np,nn), 1n+dp}` only, and no
unconditional distributive law exists in rat.bend at all -- while a `QExt.mul`
coordinate is `Rat.add(Rat.mul(..), Rat.mul(..))`, an mk-headed sum of mk-headed
products, and `==` on Rat is structural. So a QExt multiplicative fill has to
expand `(a*c + d*(b*e))*f`, which is distributivity at three arbitrary Rats; the
canonical law cannot be instantiated there, and no value law or bridge turns an
arbitrary Rat into a canonical one. The rung-2 distributive block (the additive
fill's *linear* Nat closing, not this one's bilinear one) is therefore the next
piece of work, and `QExt.mul_assoc` is downstream of it. The inverse
`1/(a + b*sqrt d) = (a - b*sqrt d)/(a^2 - b^2 d)` is not started; and
`QExt.add_assoc` **is** the form over arbitrary values now: same key, statement
replaced, and its fill is one `Rat.add_assoc.arb` per coordinate with the six
positivity hypotheses spent three per coordinate. The canonical statement is gone
rather than kept beside it, because at this layer the general form *does*
subsume it (a canonical caller supplies each hypothesis with `{==}`, since
`Rat.denof(Rat{Rat.num(np,nn), 1n+dp})` is `1n+dp`) -- unlike the Rat layer, where
the canonical `Rat.add_assoc` stays stated because its positivity slot is empty.
Two new `def`s came with it, `QExt.re`/`QExt.im`, since a statement has no body to
put the destructuring match in.

## The rung-2 multiplicative law landed, and the analysis was half right (measured)

`Rat.mul_assoc.arb` is in `rat.bend` and filled in `rat_proofs.bend`: arbitrary
`Rat` variables `x`, `y`, `z` with `{Nat.cmp(0n, Rat.denof(_)) == LT{}}` on each
of the three, conclusion `mul(mul(x,y),z) == mul(x,mul(y,z))`. Counts move as the
README records: rat 199 -> 201, qrat 204 -> 206 (the new law is
`Rat.mul.value.mixed`; the canonical `Rat.mul_assoc` stays *stated*, its fill
unchanged, and no call site moved). The six gates are green.

**What the earlier analysis got right.** The raw product pair of two coordinate
pairs *is* a constructor: after the level-2 match,
`Int.mul(Int{a1,b1}, Int{a2,b2})` reduces by itself to
`Int{add(mul(a1,a2),mul(b1,b2)), add(mul(a1,b2),mul(b1,a2))}`, so the additive
fill's two `Int.mul_scale` steps and its whole sum-assembly block have no
counterpart -- measured as the `{==}` steps in `Rat.mul.arb.coords` and by the
absence of any shape law from the fill. And `Rat.mk.value` does name its
numerator in `Rat.num` spelling, so the raw-pair presentation has to be reached
by a value equation and not by conversion -- also measured.

**Where it was wrong, in both directions.** The old comment said the fill "goes
through `Rat.mk.trunc` and `Rat.mk.rep`, exactly as the additive one does" and
that "no new value lemma is needed". Measured: `Rat.mk.rep` alone bridges the
inner product (`mk(Int{U1,V1},d1)` against `mk(Rat.num(U1,V1),d1)`; `mk.trunc` is
its truncation-spelled twin and was *not* used), and a new value law **was**
needed -- `Rat.mul.value.mixed`, whose right side is the raw product pair
`mk(Int.mul(Int{P1,Q1}, Int{Zp,Zn}), d*D)`. What makes that law cheap is the same
constructor fact: the additive twin's cross block (`Rat.add.mixed.cross` over a
sum of scaled pairs) collapses to a pure ring permutation with no sums in it
(`Rat.mul.mixed.cross`, eleven steps). The law's fill is then the additive fill's
four pieces with the cross swapped.

**The Nat closing is where the port genuinely fails, and the reason is linearity
versus bilinearity.** The additive law's two sides have coordinates
`P1*Zd + a3*(Xd*Yd)`: a *linear* combination, so the padded equations scale to
them directly and the shared padding reconciles with `Rat.nat.pad`. The
multiplicative coordinates are `P1*a3 + Q1*b3`: the *bilinear* contraction of the
truncated pair with the third factor's pair, so the two sides are different
products of the same six numbers and what reconciles them is an associativity
identity, not a padding. Three helpers carry it:

- `Rat.nat.mulpad`, from one `Nat.sub_cross` instance `p + v = q + u`, gives
  `(p*r + q*s) + (u*s + v*r) = (u*r + v*s) + (p*s + q*r)` -- each side's
  contracted coordinates plus the rest of the two pairs' products as padding.
  The proof is `Nat.mul_add_left` twice per side plus `Rat.nat.swap`.
- `Rat.nat.mul3` cancels the two paddings against each other. This is exactly
  `Int.mul_assoc.pos` and `Int.mul_assoc.neg` -- the laws the *canonical*
  `Rat.mul_assoc` fill already had -- read at the six raw coordinates, plus four
  `Nat.mul_comm` steps and one exchange of the two groups.
- `Nat.add_cancel` then strips the common padding from the two combined
  equations, and `Rat.nat.scale.eq.r` puts the result in the D-scaled form
  `Rat.mk.eqv.val` consumes.

**Checker rules this round paid for (all measured).**

- `Equal.sym`'s first argument is the type of its two endpoints. Passing `Nat`
  for `Int` endpoints produces an *empty* error message -- just `Error:` and a
  location -- which is what an ill-typed type argument looks like.
- A hypothesis binder without `+` is linear. Using it twice gives
  `expected : h / observed : h (consumed more than once)`; `+h` is the fix.
- In a nested `Equal.trans` the *declared* middle endpoint must be the term the
  first evidence actually produces, not the term the chain is heading for.
  Writing the final form there makes the checker demand that the first evidence
  span the whole chain, and writing an outer endpoint that disagrees with the
  inner chain's end makes it demand the inner chain's type one level up. Both
  were hit and both are fixed by spelling the intermediate exactly.
- `Int.mul` of two constructor pairs reduces, so `{==}` can carry a step whose
  two sides differ only by that unfolding. The additive fill's `Int.mul_scale`
  calls exist because one of its factors is a *unit* (`Int{d,0n}`), where the
  reduction leaves `mul(x,0n)` stuck; with two general pairs there is no such
  residue and no law is needed.

## The rung-2 distributive laws landed, and the closing was already there (measured)

`Rat.mul_distrib.arb` and `Rat.mul_add_left.arb` are in `rat.bend`, filled in
`rat_proofs.bend`. Counts: rat 201 -> 203, qrat 206 -> 208. Six gates green.

**The canonical fill's closing transposed verbatim, which was the one thing this
round did not have to build.** `R.Rat.mul_distrib`'s right-hand chain (M1/M3
through `Rat.mk.rep`, `pos_witness` and `Rat.add.value` to UR), its pure Nat
identity (T) from `Rat.nat.distrib`, and its two `mk.eqv.val` comparisons are
stated over terms this law has too: U1,V1 and U3,V3 are the same two products'
coordinates, U2,V2 the same sum's raw coordinates, P1/Q1/P3/Q3 the same
truncations, and UR's coordinates and denominator (P1*d3 + P3*d1 over d1*d3) come
out identical -- so `T`, `cross2f`, `val2` and r1/r2/r3 are the canonical calls
with only the two positivity arguments changed from `{==}` to the hypotheses.
`Rat.mul_add_left.arb` is the canonical mirror's three-step derivation.

**The left side is the new part, and the mixed value law does it in one call.**
The canonical fill computes `mk(Int{TLp,TLn}, Xd*m2)` -- the div/gcd-spelled
numerator mk's own reduction produces -- and bridges it to UL with a third
`mk.eqv.val` at `Rat.nat.cross1`'s cross sum, which needs `Rat.value.scaled` and
the value equation's two scaled coordinates. Here `Rat.mul_comm` (to put the
mk-headed sum on the left, where `Rat.mul.value.mixed` takes it), `Rat.mk.rep`
(to re-spell the sum's raw pair as its truncation pair) and that one law land
directly on `mk(Int.mul(Int{P2,Q2}, Int{a1,b1}), d2*Xd)`, whose pair is UL's up
to four `Nat.mul_comm` steps inside the two coordinates. No cross1, no
value.scaled, no div/gcd spelling anywhere -- the same saving the multiplicative
assoc fill got, for the same reason.

**One more checker rule, measured.** In a `%`-free chain every intermediate has
to be *written*: the second coordinate's rewrite here is two steps
(c2 -> c2b -> c2c), and passing only the second step's evidence to the cong that
consumes the first step's result fails with the expected/observed pair showing
the skipped intermediate. Unlike the `%` orientation rule this one is not a trap
in the checker -- it is just that a cong's evidence must have the endpoints the
cong names.

## The QExt multiplicative laws landed (measured)

`QExt.mul_assoc` and `QExt.mul_distrib` are in `qrat.bend`, filled in
`qrat_proofs.bend`. Counts: rat 203 -> 205, qrat 208 -> 212. Six gates green.

**The blocker was exactly the one predicted, and two more Rat laws closed it.**
`Rat.mul_distrib`/`Rat.mul_add_left` are stated over `Rat{Rat.num(np,nn), 1n+dp}`
only, and a `QExt.mul` coordinate is `Rat.add(Rat.mul(..), Rat.mul(..))` -- an
mk-headed sum of mk-headed products -- so the QExt fills need the rung-2
distributive laws, which is what the previous section landed. They also need two
more facts that did not exist: **`Rat.mul.den.pos` and `Rat.add.den.pos`**, the
positivity of a product's (resp. a sum's) denominator from its operands'. Every
rung-2 law takes `{Nat.cmp(0n, Rat.denof(t)) == LT{}}` for *three arbitrary*
Rats, and a QExt coordinate is a product of products, so a fill that instantiates
them has to build those facts itself -- and it cannot call `Rat.div.pos`, which
is a proof-only helper of rat_proofs.bend and unreachable from a third file
(measured again this round: `Rat.div.pos` there fails with "expected : a defined
name"). Both new laws' fills are one `Rat.div.pos` at the coordinates mk
destructures, with the second destructuring level written out because `Int.mul`
(resp. `Int.add` of two scaled pairs) is stuck while its arguments are variables.

**A stale checker note, remeasured.** `qrat_proofs.bend`'s header recorded that a
`cong` whose function is a lambda cannot be handed to anything -- four
measurements, and the conclusion that every fill had to be a whole-coordinate
rewrite or a def with the position as a parameter. That is no longer true:
lambda congs check as a def body, as an argument of `Equal.trans`, and nested
under another cong, in a third file importing rat.bend and rat_proofs.bend. The
old measurements were symptoms of the alias-prefixed helper names that same
header describes; with those renamed bare, all three placements check, and
`QExt.mul_assoc.re`/`.im` below are built out of them. The header is corrected in
place.

**What each fill is.** `QExt.mul_assoc` is two coordinate chains. Both sides of
each are expanded to the same flat sum of four products by `Rat.mul_assoc.arb`,
`Rat.mul_distrib.arb` and `Rat.mul_add_left.arb`, and the two groupings are
reconciled with `Rat.add_assoc.arb`/`Rat.add_comm` (a five-step rearrangement,
the same shape the rung-2 distributive fill uses for its own two groupings).
`QExt.mul_distrib` is the same shape with two `Rat.mul_distrib.arb` calls per
coordinate (three for the real one, where the radicand coefficient also
multiplies a sum) and no associativity shuffle at all. The radicand coefficient
`QExt.nat(d)` is `Rat{Rat.num(d,0), 1}`, so its denominator's positivity is
`{==}` at every call site, by computation.

## The negation laws landed, and the shape the previous round stated was not the provable one (measured)

`Rat.mk.diag`, `Rat.mul_neg` and `Rat.add_neg` are in `rat.bend`, filled in
`rat_proofs.bend`. Counts: rat 205 -> 208, qrat 212 -> 215. Six gates green
(nat, int, qext, rat, qrat `*_proofs.bend` and `scratch.bend`).

**The round before this one ended red, and the rerun said so.** Both
`rat_proofs.bend` and `qrat_proofs.bend` failed at `Rat.mk.diag` with the same
error: the fill's first `Equal.trans` declared `0n` as the middle endpoint of a
cong that actually produces `add(0n, u)`, and the file also called a
`Rat.mk.split` helper that does not exist. That is the nested-`trans` rule
already recorded in the gotchas -- the declared middle must be the term the
first evidence produces -- plus its usual cause, a chain written before it was
checked. `Rat.mul_neg`'s fill was ill-typed (`R.Rat.mul(xn, ...)` with `xn` an
`Int`) and `Rat.add_neg` had no fill at all, so the previous round's
"Six gates green" was never true of the tree it left. Everything below starts
from that measurement.

**`Rat.mk.diag` is one chain and no new machinery.** The divisor collapses
because `mag(T,T) = (T-T) + (T-T) = 0` and `gcd(0,d) = d`, both coordinates of
the numerator are `div(0,G) = 0`, and the denominator is `div(d,d) = div(1+ap,
1+ap) = 1` -- four congs, `Nat.sub_self`, `Nat.div_zero`, `Nat.div_self` and
`pos_witness` for the successor spelling. Two of the endpoints in the previous
attempt were also *oriented* the wrong way (`Equal.sym` supplies `b == a` from
`a == b`, and the fill had used it where the cong needed the forward direction),
which is the orientation rule the file's gotchas already carry.

**`Rat.mul_neg` is not a congruence law, and the reason is not the arithmetic.**
The two sides' *raw* numerators do line up -- `Int.mul(xn, Int.neg(yn))` and
`Int.neg(Int.mul(xn,yn))` are the same constructor pair, and a probe in
`rat_proofs.bend` confirmed the checker reduces both of them at concrete
coordinates -- but `Rat.mul` destructures its second argument, and `Rat.neg(y)` is
`mk(Int.neg(yn), yd)` with `Int.neg(yn)` *stuck* while `yn` is a variable, so
`numof` cannot fire and the goal never reduces to the congruence shape the
block at the top of `rat.bend` uses. What makes the law cheap instead is that
negation is multiplication by -1:

    Rat.neg_eq_mul_negone:  -y = (-1)*y

an **unconditional** helper whose fill is two congs. Both sides are `Rat.mk` of
raw pairs once `y` is destructured -- `Int{ynn,yp}` over `yd` against
`Int{add(ynn,0), add(yp,0)}` over `add(yd,0)` -- and the pairs differ by one
`Nat.add_zero` per coordinate. That is a *measured* statement about how much the
checker computes: a probe def asserted `Rat.mul(Rat.neg(Rat.one()),
Rat{Int{5,3},2}) == Rat.mk(Int{add(3,0), add(5,0)}, add(2,0))` with body `{==}`,
and it checked, i.e. `Rat.neg(Rat.one())` reduces to the constructor
`Rat{Int{0,1},1}` (through `gcd` and `div`), `Nat.mul(1n, a)` reduces to
`add(a, 0n)`, and `add(0n, a)` reduces to `a`. With the helper, the law is

    x*((-1)*y) = (x*(-1))*y = ((-1)*x)*y = (-1)*(x*y)

-- `Rat.mul_assoc.arb` read backwards, one `Rat.mul_comm` under a cong,
`Rat.mul_assoc.arb` again, and the helper read backwards. Five steps, no value
law, no cross sum, no div/gcd spelling, no Int or Nat arithmetic.

**So the law's *statement* changed, and that is the honest part of the round.**
`Rat.mul_assoc.arb` is conditional at arbitrary values, so this route proves
`mul_neg` only under the positivity of `x`'s and `y`'s denominators; the
previous round had stated it unconditionally ("for *every* pair of Rats", with a
comment claiming the Int laws identify the two raw numerators, which is the
observation above that the checker cannot use). The statement now carries the
two positivity hypotheses -- the same rung-2 hypothesis pair every other
arbitrary-value law in the file carries, and the same one the QExt layer already
states about its coefficients -- and the comment says why. One junk instance was
evaluated by hand (`x = Rat{Int{1,0},0}`) and both sides agree there, so the
unconditional form is not *known* to be false; it is simply not reachable by this
route, and the value machinery that could reach it is the route the previous
round was already stuck on.

**`Rat.add_neg` was restated too, and for a harder reason: the canonical form
the previous round wrote was unusable downstream.** It was stated as
`Rat.add(Rat{Rat.num(np,nn), 1n+dp}, Rat.neg(...)) == Rat.zero()` with
`gcd(mag(np,nn), 1n+dp) = 1` as a hypothesis. But the rationalization needs this
law at `Rat.mul(xa, xb)` -- an mk-headed product, not a canonical
`Rat{Rat.num(np,nn), 1n+dp}` -- so the canonical statement cannot be instantiated
where it is needed, and coprimality of a product is not something a caller can
have. The law is now `for +x: Rat, for +px: {Nat.cmp(0n, Rat.denof(x)) == LT{}}`,
and the coprime hypothesis turned out to be unnecessary: with the *raw*
coordinates in hand, the closing is pure Nat truncation arithmetic.

The fill is the one the previous round's comment predicted, in the order it
predicted (`Rat.mul_comm` to put the mk-headed summand in the slot the mixed
value law takes, then `Rat.mk.rep` to re-spell the raw numerator `Int{xnn,xp}` as
the truncation pair `Rat.num(xnn,xp)`), and everything after
`Rat.add.value.mixed` is the diagonal:

    C1 = (Sb*xd + Sa*0) + (xp*xd + xnn*0)
    C2 = (Sb*0 + Sa*xd) + (xp*0 + xnn*xd)          Sb = xnn - xp,  Sa = xp - xnn

Five Nat steps per coordinate (four congs -- two `mul_zero`, two `add_zero` --
around `Nat.mul_add_left` read backwards) bring both to
`mul(add(Sb,xp), xd)` and `mul(add(Sa,xnn), xd)`, and `Nat.sub_cross` at
`cmp(xnn,xp)` says the two inner sums are equal, so `Equal.cong` under `mul(.,xd)`
closes it. Then `Rat.mk.diag(C1, xd*xd, Nat.mul_pos)` is the whole denominator
side. No value equation, no cross sum, no coprimality, no case analysis.

**One call-site spelling, measured once.** `Rat.add.value.mixed`'s `pq`
hypothesis is the positivity of `Rat.denof(Rat.mk(Rat.num(np1,nn1), d))`, and
that gcd is over the *truncation pair's* coordinates:
`Rat.g(Nat.sub(np1,nn1), Nat.sub(nn1,np1), d)`, not `Rat.g(np1,nn1,d)`. Passing
the raw-pair spelling fails with the expected/observed pair naming both gcds
(`add(sub(sub(xnn,xp),sub(xp,xnn)), sub(sub(xp,xnn),sub(xnn,xp)))` against
`add(sub(xnn,xp),sub(xp,xnn))`), because `Rat.mk` destructures what it is handed
and `Rat.num` is already the difference pair. This is the same second-destructuring
fact the `den.pos` fills record, at a call site rather than in a helper.

**What the three laws are for.** `Rat.mul_neg` (at `xa,xb`), `Rat.mul_neg` again
(at `xb,xb` and at `D, mul(xb,xb)`) and `Rat.add_neg` (at `mul(xa,xb)`) are
exactly the Rat-level facts of the division-free rationalization
`x * conj(x) = a^2 - b^2 d`: the imaginary coordinate
`xa*(-xb) + xb*xa` is `-u + u = 0` at `u = xa*xb`, and the real coordinate needs
`xb*(-xb) = -(xb*xb)` and then `D*(-(xb*xb)) = -(D*(xb*xb))`. The QExt side
(`QExt.conj`, `QExt.norm` and the law itself) is the next unit; the literal
division form additionally needs a `Rat` inverse operation with its own laws,
which is still open.

## The division-free rationalization landed (measured)

`QExt.conj`, `QExt.norm` and `QExt.mul_conj` are in `qrat.bend`, filled in
`qrat_proofs.bend`. Counts: rat 208 (unchanged), qrat 215 -> 216. Six gates
green.

**The law is four Rat laws wide, and all four are from the negation block.**
With the coefficients destructured as `QExt{xa,xb}`, `QExt.mul(d, x,
QExt.conj(x))` unfolds to `QExt{xa*xa + D*(xb*(-xb)), xa*(-xb) + xb*xa}` with
`D = QExt.nat(d)` (a stuck term is enough: `QExt.mul` destructures its third
argument, which `QExt{xa, Rat.neg(xb)}` still is -- the negative is only stuck
*inside* a field). The real coordinate is then

    xa*xa + D*(xb*(-xb))  =  xa*xa + D*(-(xb*xb))     Rat.mul_neg(xb,xb)
                          =  xa*xa + (-(D*(xb*xb)))    Rat.mul_neg(D, xb*xb)
                          =  Rat.sub(xa*xa, D*(xb*xb)) {==}

and the imaginary one

    xa*(-xb) + xb*xa  =  (-(xa*xb)) + xb*xa           Rat.mul_neg(xa,xb)
                      =  (-(xa*xb)) + xa*xb           Rat.mul_comm(xb,xa)
                      =  u + (-u)                     Rat.add_comm
                      =  0                            Rat.add_neg(u)

-- i.e. no distributivity, no associativity, no value law and no cross sum
anywhere: the rationalization is exactly the two negation laws applied to the
conjugate pair. Both coordinates need a positivity fact that is not a
hypothesis, and `Rat.mul.den.pos` is what supplies it (`mul(xb,xb)` in the real
chain and the mixed law's product `mul(D, E)`, `mul(xa,xb)` for `Rat.add_neg`);
`QExt.nat(d)`'s own denominator is 1, so `{==}` discharges that slot.

**A new checker fact, measured on the first attempt.** A *def* whose body reads
the same argument twice has to declare that parameter `+`: `QExt.conj(x)` (which
calls `QExt.re(x)` and `QExt.im(x)`) and `QExt.norm(d,x)` (four reads) both
failed with `expected : x / observed : x (consumed more than once)` until the
parameter was written `+x`. Law fills inherit their linearity from the law, so
this only shows up on new helper defs -- `QExt.re`/`QExt.im` were already
`(+a, +b)` for the same reason.

**The QExt assembly is the same three-endpoint trans as every other QExt law**
(`qext.re` then `qext.im`), so the fill is two coordinate chains plus two lines
of gluing. The statement's right side is `QExt{QExt.norm(d,x), Rat.zero()}` and
the fill's is the same term with `Rat.sub` unfolded -- the def is transparent, so
the two spellings are one conversion apart.

**What is still open on this route.** `1/(a + b*sqrt d) = conj(x)/norm(d,x)`
needs a `Rat` inverse: the operation, its laws, and the `Rat` division that
consumes it. That is the field-axioms-and-inverse unit the README already names,
and nothing in this round shortens it.

## The inverse unit, round one: the operation and the two orientation rules

`Rat.inv` and `Rat.div` are in (commit `bbbef5f`), the GT branch of
`Rat.mul_inv` is stated and its arithmetic is in place -- `Rat.mul.num.coords`,
`Rat.mul.mag.coords`, `Rat.mul_inv.gt.pw`, `Rat.mul_inv.gt.divself`,
`Rat.mul_inv.gt.hT`, `Rat.mul_inv.gt.chain` all check -- and the one step still
red is `Rat.mul_inv.gt.gT`, which is `gcd(T, T) = T`. Everything below was
measured, not reasoned about; two of the statements contradict the earlier
notes in this file, so they are worth folding back into the gotchas.

**`Equal.sym(A, a, b, e)` for `e : {a == b}` gives `{a == b}`** -- it does *not*
flip. `Equal.sym(Nat, p, Nat.mul(p, 1n), N.mul_one(p))` is `{p == Nat.mul(p,1n)}`,
the same as its argument, and swapping `a` and `b` gives the other direction.
The `%`-ascription convention is likewise the reverse of what earlier rounds
recorded: `%e : {_ == a : A}` rewrites occurrences of `a` (the LHS inside the
ascription) with `b`, so a rewrite fires *left-to-right* by its own statement.

**`Equal.cong(f, a, b, e)` for `e : {a == b}` gives `f(b) == f(a)`.** Measured
twice: with `f = u => Nat.add(p, u)`, `a = p*dp`, `b = dp*p` and
`Nat.mul_comm(p,dp) : {a == b}`, the result is `add(p, dp*p) == add(p, p*dp)`.
This is the orientation the fills have to be written in, and it is why the
`cong` at a goal whose arguments are *not* abstract variables wants its evidence
oriented the other way round.

**`Nat.mul_one` in this repo is stated flipped.** `nat.bend` has
`law mul_one: {a == Nat.mul(a, 1n)}` with an explicit note that it is stated
flipped so rewrites fire left-to-right. A fill that wants `mul(a,1n) == a` has
to build it, and one that wants `a == mul(a,1n)` takes the law as it is.

**`Nat.div` and `Nat.gcd` arguments cannot be reached by a `%` rewrite at all.**
Both are defs whose bodies call `.fin`/`.go`, so a goal's occurrence shows up as
`div.fin(divmod(..))` or `gcd.go(..)` while the rewrite's pattern is the
abbreviated call -- the matcher has nothing to match on. `Nat.mul` arguments are
worse than that: they sometimes reduce and sometimes do not, depending on how
much of the surrounding context is already constructor-headed, so a proof that
leans on that reduction at one site and not another is fragile. The reliable
route is `Equal.cong` at each position, with the two orientations above, and
`Equal.trans` with the middle endpoint spelled exactly as the first half's
result rather than as something merely equal to it.

**What is left for `Rat.mul_inv.gt`.** `gT` is the only red step: with
`hT : {T == Nat.add(Nat.mul(p,1n), Nat.mul(p,dp))}`, the goal is
`gcd(T,T) = T`, and the pieces are `mul_one` to put both arguments at `T*1`,
`hT` to turn the second into `mul(p*1 + p*dp, 1)`, `Nat.mul_comm(1n+dp,p)` to
order that one as `mul(p, 1n+dp)`, the outer `gcd_scale` to factor out `p`, and
the inner `gcd(d',d') = d'` from `gcd_scale` at `k = 0`. Each of those five
steps is a three-line `Equal.trans` once the orientations above are applied;
what is red is the composition, not the arithmetic. The `T = mul(1n+dp, p)`
call site is where the two spellings of the argument (`mul(T,1n)` and
`1n + add(dp,0)`) have to be reconciled, which is the last `cong` in the chain.

**The LT branch and `Rat.div_mul_cancel` are untouched.** `Rat.mul_inv.lt` is
stated (with the hypothesis `{LT{} == Nat.cmp(np,nn)}`, the orientation
`Rat.inv` consumes) and has no fill; `rat.bend` reports 210 TODOs, i.e. the two
branch laws and nothing else.

**Gate state at the end of this round: red, by design of the checkpoint.** The
two branch laws `Rat.mul_inv.gt` and `Rat.mul_inv.lt` are *stated* in `rat.bend`
and their fills are not in `rat_proofs.bend` -- the GT fill is parked in
`wip-inv.bend`, which nothing imports, because a red fill takes every gate down
with it. So the counts are now nat 127, int 32, qext 34, **rat 210**, **qrat
218**, and the five proofs files plus `scratch.bend` fail with
`Error: 2 TODOs found.` (the two stated laws) until the fills land. The counts
before this round were rat 208 / qrat 216, and the earlier note in this file
that says "208" belongs to that state.

**What is measured and what is not.** In `wip-inv.bend`: `Rat.mul.num.coords`,
`Rat.mul.mag.coords`, `Rat.mul_inv.gt.pw`, `Rat.mul_inv.gt.divself`,
`Rat.mul_inv.gt.hT` and `Rat.mul_inv.gt.chain` all check; `Rat.mul_inv.gt.gT`
does not, and it is the only red def in the file. The LT branch has no fill at
all. To go back to a green tree without finishing the law, delete the two `law
Rat.mul_inv.*` blocks from `rat.bend`; the defs from `bbbef5f` are independent.

### The rewrite and orientation rules, measured (supersedes the earlier notes)

Four rules, each measured directly in this repo with a two-line probe rather
than read off a proof; the earlier gotchas in this file state two of them the
other way round, which cost several failed rounds.

- **`%e : P` rewrites left-to-right by `e`'s statement.** With
  `e : {a == b}`, a goal containing `a` becomes the goal with `a` replaced by
  `b`. The `_` in an ascription such as `%e : {_ == a : A}` is the *occurrence*
  side, not a wildcard for the produced type: `{_ == a}` marks the position the
  matcher searches, and the replacement is `e`'s other side. So the spelling
  `%e : {_ == Nat.div(T, T) : Nat}` is what you want when the goal's occurrence
  is `Nat.div(T,T)` and `e` says `div(T,T) == q`.
- **`Equal.sym(A, a, b, e)` returns `{a == b}`** for `e : {a == b}` -- it does
  not flip. To flip, swap the two middle arguments:
  `Equal.sym(A, b, a, e) : {b == a}`. A probe confirms both directions; the
  consequence is that a `sym` whose result is not used in the same orientation
  as its argument's statement is a no-op on the type.
- **`Equal.cong(f, a, b, e)` for `e : {a == b}` returns `f(b) == f(a)`.** With
  `f = u => Nat.add(p, u)`, `a = Nat.mul(p,dp)`, `b = Nat.mul(dp,p)` and
  `Nat.mul_comm(p,dp) : {a == b}`, the result is
  `add(p, dp*p) == add(p, p*dp)`. The `a` and `b` arguments are *the endpoints*
  -- passing them in the order you want the equation is what produces the
  reversed equation, which is where most of the failed rounds went.
- **`Nat.mul_one` is stated flipped**: `nat.bend` has
  `law mul_one: {a == Nat.mul(a, 1n)}` with a note that this is deliberate so
  rewrites fire left-to-right. A fill wanting `mul(a,1n) == a` has to flip it.

Two structural facts that decide what is even writable:

- **A `%` rewrite cannot reach an argument of a def whose body is a nested
  call.** The goal's `Nat.div(a,b)` shows up to the matcher as
  `Nat.div.fin(Nat.divmod(a,b))` and the goal's `Nat.gcd(a,b)` as
  `Nat.gcd.go(...)`, while a lemma's statement is the abbreviated call; the
  matcher has nothing to match on. Reach those positions with `Equal.cong` at
  that exact position instead. `Nat.mul` arguments are worse: they reduce or do
  not depending on how constructor-headed the rest of the context already is,
  so a fill that relies on that reduction at one site and not at another is
  fragile, and the fix is to write the lemma's own spelling out.
- **`Nat.gcd_scale` is stated at `gcd(mul(m, 1+kp), mul(d, 1+kp))`**, not at
  `gcd(m, d)` -- a caller whose gcd argument is `t` has to write `t` as
  `mul(t, 1n)` first (`Nat.mul_one` flipped), and the endpoints of that rewrite
  are the *go-form* of the gcd, so `{==}` opens the chain and the stated type is
  reachable only through the abbreviation. This is where `Rat.mul_inv.gt.gT`
  stood red until round two, where a Nat-level law replaced the in-file
  reconstruction.

## The inverse unit, round two: gcd_self as a law, and a false statement under the first red (measured)

Round one ended by saying that everything in `wip-inv.bend` except `gT` checks.
That was read off "the first error is in `gT`", and the checker reports only the
first error in file order -- so it was an inference, not a measurement. Carrying
out the `gT` recipe with a Nat-level law instead of the in-file reconstruction
removed that error, and the defs underneath it were not in the state the
inference described.

**`Nat.gcd_self` is a law now, and it is what `gT` needed.** `nat.bend` carries

    law gcd_self:
      for +a: Nat
      {Nat.gcd(a, a) == a : Nat}

filled in `nat_proofs.bend`: `match a`, `0n` is `{==}`, and the successor case is
two lines -- `%NL.add_zero(1n+ap) : {NL.Nat.gcd(_, _) == _ : Nat}` and then
`NL.gcd_scale(1n, 1n, ap)`. One `gcd_scale`, not two: `Nat.mul(1n, 1n+ap)`
reduces to `Nat.add(1n+ap, 0n)`, which is the `mul(m, 1+kp)` spelling
`gcd_scale` is stated at, and `Nat.gcd(1n, 1n)` reduces to `1n` on its own, so
that instance's statement *is* the case goal. The law's `for +a` is also what
lets the bare-name fill read `ap` twice: a linear `def g(a)` fails with
"ap (consumed more than once)".

The generality is the whole reason the law exists. At the *variable* `p` the
in-file version was stuck -- `Nat.cmp(p, p)` is stuck, so the loop cannot start
-- and a lemma stated at `1n+dp` is a different, non-convertible type. Measured
as the error it produced: `Nat.gcd(p, p) == p` expected against
`Nat.gcd.go(1n+Nat.add(p, 1n+p), 1n+p, Nat.cmp(p, p), 1n+p) == 1n+p` observed.
`Rat.mul_inv.gt.gself` is gone from `wip-inv.bend`; `gT` reaches `Nat.gcd_self(p)`
through one `Equal.cong` over `u => Nat.mul(u, 1n+dp)` and checks.

Counts after the law: nat 127 -> **128**, rat 210 -> **211**, qrat 218 -> **219**
(int 32, qext 34 unchanged), all six gates in their expected states.

**`Rat.inv`'s LT and GT branches dropped `d`, so both laws were false as
stated.** Both branches spelled the numerator out of `np`/`nn` --
`Rat{Rat.num(np, nn), Nat.sub(np, nn)}` on GT, the mirror on LT -- where the
reciprocal needs `d` in that slot: the branch's own comment says the result is
`d/(np-nn)`, "the pair `(d, |np - nn|)` is already reduced", and the header of
`wip-inv.bend` assumes exactly that shape (`Int{p*d', 0}` over `d'*p`). As
committed, `Rat.inv` returned the *value* 1 for every non-zero input. Measured
with the law's instance as a `{==}` goal: GT at np=5, nn=3, dp=0 gives
`Rat{Int{2n,0n}, 1n}` expected against `Rat{Int{1n,0n}, 1n}` observed (2 = 1);
LT at np=3, nn=5, dp=0 gives `Rat{Int{0n,2n}, 1n}` against `Rat{Int{1n,0n}, 1n}`
(-2 = 1). Fixed to `Rat{Rat.num(d, 0n), Nat.sub(np, nn)}` (GT) and
`Rat{Rat.num(0n, d), Nat.sub(nn, np)}` (LT); the same three instances then check
by `{==}` alone (np=5, nn=3 at dp=0 and dp=2; np=3, nn=5 at dp=0), including
`Rat.num(1n + 2n, 0n)` -- the `sub` terms inside `Rat.num` reduce on their own at
a successor `d`. All six gates are unchanged by the fix, and inside `src/` the
only caller is `Rat.div`.

**What the tail of `wip-inv.bend` actually is.** With `gT` green the first error
is `chain`, and it is a statement error: `Rat.mul_inv.gt.chain` states
`R.Rat{R.Rat.num(T, T), Nat.div(T, T)} == R.Rat.one()`, whose left endpoint
reduces to `R.Rat{Int{0n,0n}, Nat.div(T,T)}` -- the diagonal pair is zero, so the
goal asserts 0 = 1. `Rat.num(T, T)` is not the product's numerator at that
position; the mk-output shape is `Int{T, 0}`, with `T = d'*p` in the first slot
and the two `div(T, T)`s still to be carried to 1. `coords` fails for two further
reasons: it calls `Rat.mul.num.coords` and `Rat.mul.mag.coords`, neither of which
is defined here or in `src/` (measured: "expected: a defined name / observed:
Rat.mul.num.coords") -- the comments at the top of the file about "the two halves
of the pair gcd_divides returns" and "the two div coordinates of the GT branch"
are what is left of them; and every `%` pattern in it carries more than one `_`,
which cannot work, because `bend.ts` types the pattern under a `Lone()` binder
(the two-hole `{Nat.gcd(_, _) == 1n+dp}` of the erased `gself` was accepted
precisely because both holes are the *same* term). Its call
`%Rat.mul_inv.gt.gT(T, {==}, p, dp)` also contradicts `gT`'s telescope
`(T, p, dp, hT)`, and `{==}` cannot be that `hT` anyway: `T` is the let
`Nat.mul(1n+dp, p)` and `Nat.mul(p, 1n+dp)` is `Rat.mul_inv.gt.hT`'s job, not a
conversion.

So the state is: `pw`, `divself`, `hT`, `gT` check; `chain`'s statement has to
be restated on the product's real numerator before its body means anything; the
two coord helpers have to be written again; `coords`' rewrite steps have to be
one hole each.

*Round three supersedes that paragraph: both branches landed, and the closing
turn out not to need the coord helpers as separate defs at all.*

## The inverse unit, round three: both branches landed, and the LT half is a mirror image (measured)

`Rat.mul_inv.gt` and `Rat.mul_inv.lt` are proved. `src/rat_proofs.bend` checks
-- `All terms check.`, not a TODO count -- and so does `src/qrat_proofs.bend`,
whose 2 TODOs were exactly these two laws. All five `*_proofs.bend` files are
green, and the tree now has no unfilled law. The workbench `wip-inv.bend` is
gone: its content is the ported block, and keeping the file would have been a
second definition of `R.Rat.mul_inv.gt`.

**What round two's ending got right, and what it guessed wrong.** `chain`'s
statement *was* wrong (it asserted 0 = 1) and it *was* restated -- but not on
the clean `Int{T, 0}` the paragraph above guessed. `Rat.mul` expands to
`Int.mul(Rat.num(np, nn), Int{1n+dp, 0n})` before `Rat.mk` normalizes, and
`Int.mul` is a four-product sum, so what the checker shows is

    ca = mul(np-nn, 1n+dp) + mul(nn-np, 0n)     cb = mul(np-nn, 0n) + mul(nn-np, 1n+dp)

with mk's denominator argument `add(np-nn, mul(dp, np-nn))`. The probe that
printed it is the technique that made this round mechanical: a `{==}` at the
*law's own instance*, which forces the checker to print both endpoints in SNF.
Measured that way, `chain` is

    def Rat.mul_inv.chain(+T: Nat, +pT: {Nat.cmp(0n, T) == LT{} : Cmp})
      -> {R.Rat{I.Int{Nat.div(T, T), Nat.div(0n, T)}, Nat.div(T, T)}
          == R.Rat.one() : R.Rat}

and its body is three `Equal.cong` steps -- `divself`, then `div_zero`, then
`divself` again -- with no `Nat.divides` witness and no destructure of the pair
`gcd_divides` returns. The old route took `Pair.fst(N.gcd_divides(T, T))`
because an anonymous pair cannot be destructured by its caller; `div_self`
reaches `div(T, T) = 1` at the opaque dividend the goal has, so that witness was
never needed for this.

**The Nat algebra under the coordinates.** With `s = sub(np, nn)`,
`t = sub(nn, np)`, the two raw coordinates and their difference reduce to `T`
and `0` (`coordA`/`coordB`, then `subAB`/`subBA`), the magnitude to `mul(T, 1)`
(`magT`), and the divisor `gcd(mag, add(s, mul(dp, s)))` to `T` (`gcdT`) -- which
is `gT` at `T := mul(1n+dp, s)`, `p := s`. The coordinates are then
`div(T,T)`, `div(0,T)`, `div(T,T)`: `chain`'s goal. The branch hypothesis is
consumed exactly once, in `coordB` (`np > nn` means `nn-np` is zero, through
`sub_of_lt` at `cmp(nn, np) = LT`); by the time the coordinates are stated, it
has been spent.

**The LT branch is the GT branch with the two raw products swapped -- measured
before a line was written.** The probe on the LT law's instance printed
`A_lt = add(mul(s, 0n), mul(t, 1n+dp))`, `B_lt = add(mul(s, 1n+dp), mul(t, 0n))`
and `D_lt = add(t, mul(dp, t))`: the same terms as GT with `A`/`B` exchanged and
`s` replaced by `t` in `D`. So `lt.coordA`/`lt.coordB`/`lt.subAB`/`lt.subBA`/
`lt.magT`/`lt.gcdT` are mirror statements, `lt.pb` flips the hypothesis with
`cmp_gt_of_lt` before `sub_pos`, and `lt.coords` is `gt.coords` with the
spellings substituted. Nothing structural differs; both branches close on the
same `chain`.

**Two rules this round paid for, both about spelling at a variable.**

- The one design that failed: a branch-agnostic wrapper
  `pos_mul(a, b, pb) -> {cmp(0n, mul(a, b)) == LT{}}` calling
  `N.mul_pos(a, b, {==}, pb)` is rejected -- `expected : Nat.cmp(0n, a)` against
  `observed : LT{}` -- because `Nat.cmp(0n, a)` is stuck at a variable, so
  `{==}` can only discharge `mul_pos`'s first-factor evidence when that factor
  is *literally* a successor. This is the `Nat.gcd_self` lesson one level down:
  a law stated at a variable cannot be reached by a proof step that only runs at
  a constructor. The fix is a per-branch `pb` plus the direct
  `N.mul_pos(1n+dp, q, {==}, pb)` at the call site, where the term is a
  successor.
- The `%` patterns. Every rewrite in `coords` is written **one hole per step**,
  with the other slots spelled at the goal's own SNF terms -- that is what the
  probe is for: the second numerator slot has to be written
  `Nat.div(Nat.sub(B, A), G)`, not `Nat.div(B, G)`. Round two's claim that a
  multi-hole pattern cannot be accepted stays untested in the direction that
  matters, because this round never needed one: a *distinct-term* multi-hole
  pattern is still an open question, and the working rule is the measured one --
  one hole per rewrite, everything else spelled exactly as the checker prints
  it.

**Naming.** `pw`, `divself`, `hT`, `gT` and `chain` lost the `gt.` prefix once
LT needed them (`Rat.mul_inv.pw` and so on); the coordinate helpers keep their
`gt.`/`lt.` prefixes, because those statements are branch-specific. `gt.pT`
split into `gt.pb`/`lt.pb` plus the direct `mul_pos` call above.

**Technique that carried the round.** The deliberately-false `{==}` at a law's
own instance, run *before* writing any proof: one run pinned the GT SNF and one
pinned the LT shapes, after which the whole LT half was written by substitution
rather than by derivation. One probe per run -- the checker stops at the first
error. `probe.bend` holds the last probe; `scratch.bend` prints the fixed
`Rat.inv` triple, `(Rat{Int{7,0}, 2n}, Rat{Int{0,7}, 2n}, Rat{Int{0,0}, 0n})`
at `(5,3,7)`/`(3,5,7)`/`(3,3,7)` -- `7/2`, `-7/2`, and the `EQ` branch's zero
numerator over `sub(np, nn)`, which is 0 at that branch. That third component is
what a zero input can get: no law is stated for `np = nn`, and the two laws are
`gt` and `lt` only.

**Left on this side of the layer.** The inverse *operation* and its two laws
are in. The division laws (`Rat.div`'s value form, and the field axioms stated
over `div`) are the next unit on the Rat side, and `QExt`'s
`1/(a + b*sqrt d) = conj(x)/norm(d,x)` is now one `Rat.div` call away.

## The division laws landed: the sign goes in the spelling, and the branch-free statement is out of reach (measured)

Ten laws of `Rat.div` are stated and proved, all five `*_proofs.bend` gates are
green, and the counts are rat.bend 221 = 128 Nat + 32 Int + 61 Rat, qrat.bend
229 (it imports rat.bend, so it moved with it). The new laws are
`Rat.div.value.gt`/`.lt`/`.eq` (the value form, one per branch of `Rat.inv`'s
split), `Rat.div_self.gt`/`.lt`, `Rat.div_one`, `Rat.div_mul_cancel.gt`/`.lt`
(`(x/y)*y = x`) and `Rat.div_add.gt`/`.lt` (`(x+y)/z = x/z + y/z`).

**The design decision, and the wall behind it.** `Rat.div(a, b)` is
`Rat.mul(a, Rat.inv(bp, bnn, bd, Nat.cmp(bp, bnn), {==}))`. At a *variable*
divisor that fifth argument is stuck, and it is stuck in the worst place: inside
`Rat.inv`'s argument list, next to the `{==}` whose type mentions it. A `%` step
cannot reach it. The pattern would have to rebuild that argument list, and the
obligation it must satisfy is the type `{x == Nat.cmp(bp,bnn)}` that `Rat.inv`
puts on its evidence slot, while a pattern's own evidence binder has type
`{GT{} == x}` -- the opposite orientation, hole on the opposite side. A derived
term -- `Equal.trans(Cmp, _, GT{}, Nat.cmp(bp,bnn), Equal.sym(Cmp, GT{}, _, e), e)`
-- does typecheck *inside* the pattern, and then dies one check later: `Rwt`'s
fit compares the evidence terms (or at least refuses a trans chain against
`{==}`), so `expected` prints the goal with `{==}` where `observed` has the
chain. Three probes, one run each; the fit is the third throw in check-rwt and
its message names the `%` span, which is how the two were told apart. So a law
*stated* with a chain-spelled instance is not the answer either: a goal that
contains `Rat.div` SNFs to the `{==}` spelling, and no equation between the two
spellings can be built.

**Therefore the sign goes in the spelling.** A positive divisor is written
`Rat{Rat.num(1n+ap, 0n), 1n+dp}` (numerator coordinates `1+ap` against `0n`), a
negative one `Rat{Rat.num(0n, 1n+bp), 1n+dp}`, and the zero divisor
`Rat{Rat.num(0n, 0n), 1n+dp}`. `Nat.cmp` then computes on constructors, `Rat.inv`
matches, and all of `Rat.div` reduces to a product by the reciprocal -- with no
rewrite at all, which is why the fills are as short as they are: the three value
laws are `{==}`, `div_self.*` is one `Rat.mul_inv` call each, `div_one` is
`Rat.mul_one`, `div_add.*` is one `Rat.mul_add_left.arb`, and only the field
axiom needs a chain (associativity, then the reciprocal pair under a `cong`,
then `mul_one`). The spelling *is* the branch evidence, exactly as in
`Rat.mul_inv` -- which is also why the branches are separate laws and no law
carries a `c != EQ` side condition.

**The one trap in the mirror.** For a negative divisor the reciprocal is
`Rat{Rat.num(0n, 1n+dp), 1n+bp}`, not `Rat{Rat.num(1n+dp, 0n), 1n+bp}` -- it is
negative too. Copying the GT spelling into the LT chain (the natural error, since
only the first coordinate of `Rat.num` differs) fails with the mismatch reported
on the *first factor of the goal's product*, not on the reciprocal:
`expected : Rat.mul(Rat.mk(Int.mul(n, Int{0n, 1n+dp}), Nat.mul(d, 1n+bp)), ..)`
against the same term with `Int{1n+dp, 0n}`. The value laws had the sign right
and the mirror did not, which is the argument for probing *both* branches with a
`{==}` value form before writing either chain.

**`x / 0` is zero, but it is not the term `Rat.zero()` -- measured.**
`Rat.div.value.eq` was written last, on the guess that the EQ branch behaves like
the other two. It does -- the comparison computes and `{==}` closes it -- but
what it says is worth recording: `x / 0` reduces to
`Rat.mk(Int.mul(xn, Rat.num(0n, 0n)), Nat.mul(D, 0n))`, the value zero in the
degenerate spelling `Rat{Int{0,0}, 0n}`, whose denominator is 0. It is not
`Rat.zero()` (= `Rat{Int{0,0}, 1n}`), and no structural `x/0 = 0` law can exist:
`{Rat.div(Rat{n, 1n+dp}, Rat.zero()) == Rat.zero()}` was run as a deliberately
false def and failed with `expected : Rat.mk(Int.mul(n, Int{0,0}),
Nat.mul(dp, 0n))` against `observed : Rat{Int{0,0}, 1n}`. A caller who wants the
constructor has to go through the value laws (`Rat.mk.eqv`), not through `{==}`.

**The laws are usable, and that was checked rather than assumed.** `probe.bend`
is now a consumer file: it imports `rat.bend` and `rat_proofs.bend`, states each
of the ten laws from the caller's side, and applies them by name -- including at
literals, which is the only way to see that the implicit arguments really are
inferable, and at variables with the branch facts as hypotheses, which is the
realistic case. It also derives a fact that is not one of the ten,

    (x + y) / 1 = x + y

by `Rat.div_add.gt` at `ap = dp = 0n` followed by two `Rat.div_one` under
congruences. The first step is the interesting one: it reaches a goal stated
with `Rat.one()` only because `Rat{Rat.num(1n+0n, 0n), 1n+0n}` is convertible to
`Rat.one()`, i.e. a law stated at the spelled-out divisor does apply to a goal
stated with the constructor. Every consumer of this block depends on that.

**What is still out of reach, and the alternative that was dropped.** There is
no branch-free law at a variable divisor: `Rat.div(x, Rat{Rat.num(np,nn),
1n+dp})` does not reduce, and the evidence wall says no rewrite opens it. A
consumer with a symbolic divisor must carry the branch as a hypothesis and use
the branch law -- the discipline `Rat.mul_inv` already imposes. The alternative
considered and dropped was to delete `Rat.inv`'s `+e` parameter, so that
`Rat.div`'s body would contain no `{==}` to compare against. It is not needed
for these ten laws, and it would not buy a variable-divisor law anyway: the
`Nat.cmp(bp,bnn)` handed to `Rat.inv` as its `c` argument is still stuck at a
variable, so `Rat.inv`'s own `match c` still cannot fire. The wall is the
comparison, not the evidence.

**Two corrections to round three's record.** Its closing paragraph says "no law
is stated for `np = nn`, and the two laws are `gt` and `lt` only" -- true of the
inverse then, and no longer true of `div`, which now has `Rat.div.value.eq`. And
its "left on this side" list carries the `Rat.inv` signature edit as the route to
a variable-divisor law; the measurements above say the sign-in-the-spelling route
is the one that works and the signature is untouched.

## The QExt division payoff landed, and the norm is not positive (measured)

The unit round four pointed at was one law: for `x = a + b*sqrt d`,

    x * (conj(x) / norm(d, x)) = 1

-- the rationalization, the reason the whole division block exists. It is now
`QExt.inv.value.gt` in `src/qrat.bend`, filled by three defs in
`src/qrat_proofs.bend`.

**Two Rat laws had to come first, and both are denominator-level.** The payoff's
rearrangements carry negations of the *coefficients* through products, so they
need the positivity of a negated denominator, `Nat.cmp(0n, denof(neg x)) == LT{}`
-- the missing third member of the `mk.den.pos` / `mul.den.pos` / `add.den.pos`
family, added as `Rat.neg.den.pos`. It is a law rather than a bridge for the
reason the family is: `Rat.neg` destructures before calling `Rat.mk`, so at a
variable the term is stuck and no congruence or `mk`-headed positivity law
reaches it. And the payoffs need negation on the *left* of a product,
`(-x)*y = -(x*y)`; `Rat.mul_neg` cannot be turned around, because its negation is
in the second factor -- so `Rat.neg_mul` was added (three steps: `mul_comm`, the
inner `mul_neg`, and a `cong` under `neg` with `mul_comm` again). The payoff uses
it three times.

**One language fact, found by failing.** A `let` cannot hold a bare constructor:

    +rh = R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}

is rejected with `expected : an annotated term (cannot infer)` and the
constructor's type in `observed` -- with no expected type, the checker cannot
infer which type the constructor builds. `let`s whose right-hand side is a *def*
call are fine, because a def has a known result type, and that asymmetry is the
whole reason `Rat.of` exists in `src/rat.bend`:

    def Rat.of(+np: Nat, +nn: Nat, +dp: Nat) -> Rat:
      Rat{Rat.num(np, nn), 1n+dp}

a plain abbreviation like `QExt.of`, nothing normalized, no match on its
arguments. With it every `let` in the fill names its divisor once.

**The law's design is round four's design.** The divisor's sign is in the
*spelling*: the norm is written as the positive raw pair `(1+ap)/(1+dp)` and a
hypothesis `hZ` says that rational *is* `QExt.norm(d,x)`. This is what buys the
fill: `Rat.div(x, spelled)` reduces by conversion to `mul(x, reciprocal)` at a
*variable* dividend -- no law, no rewrite. Measured before the fill was written,
by a `{==}` against that goal at variables; `probe.payoff.bend` keeps it as the
first of its three defs.

**The fill.** Two coordinate defs plus the composing chain.
`QExt.inv.value.gt.re` is stated in the *unfolded* shape -- the goal after the
`Rat.div`s have become products by the reciprocal -- and is a rearrangement:
associativity twice (read backwards), `mul_neg`, then a three-`Equal.trans`
chain that pulls `D*(neg BB*rh)` to `neg(PP)*rh` via `neg_mul`, `mul_neg` and an
associativity under a `neg` congruence, `mul_add_left` backwards to re-fold the
sum, `{==}` twice to cross the `sub`/`add-neg` and `norm` spellings, a `cong`
with `sym(hZ)` to re-spell the norm as the literal pair, and `Rat.mul_inv.gt` at
`(1+ap, 0n, dp)` to close. `QExt.inv.value.gt.im` is the mirror and cancels
without needing `hZ` at all (`add_comm`, `add_neg`). The composing def matches
`x` into `(xa, xb)` and then

    trans(QExt{Lr,Li}, QExt{one,Li}, QExt{one,zero})

-- the `re` step at the first coordinate only, the `im` step at the second. The
first version tried to go straight to `QExt{one,zero}` and the checker answered
with `expected : QExt{one, zero}` / `observed : QExt{one, Li}`: the intermediate
has to keep the coordinate the current step is not touching, exactly as
`QExt.mul_conj`'s fill does.

**One realization that saved a step.** After `match x`, the law's own
left-hand side -- `QExt.mul(d, x, QExt{div, div})` -- reduces to
`QExt{Lr,Li}` definitionally, so the chain starts at the matched pair with no
`{==}` bridging step.

**Where the statement stops, measured.** An earlier comment in `rat.bend` said
the norm `a^2 - b^2*d` of a non-zero extension is positive, and that the GT
branch is the branch a rationalization caller has already decided. The second
half is false in `d` itself: the norm is indefinite, so an extension like
`1 + 2*sqrt 3`, whose norm is `-11`, has no positive raw pair equal to its norm
-- no `hZ` exists, and no GT law can state that instance. What is measurable is
the product against the *positive* spelling `11`, and it is not 1: deliberately
false `{==}` on the closed product prints

    expected : QExt{Int{0,1}/1, 0}      (i.e. -1 over 1)
    observed : QExt{Int{1,0}/1, 0}      (QExt.one())

so the same product built with `11` multiplies out to **-1**. That is the
boundary of the law, not a presentational choice, and it is why an LT twin of
`QExt.inv.value.gt` is the next unit. Both files' comments were corrected to say
this instead.

**What checks, and the counts.** All five `src/*_proofs.bend` print
`All terms check.`, as do `probe.bend` and the new `probe.payoff.bend`
(which states the conversion, the law from a caller's side at a *variable* `x`,
and the literal `1/(2 + sqrt 2) = (2 - sqrt 2)/2`). Two honest notes about that
probe: at literals the whole product *also* reduces on its own -- measured,
`{==}` closes the instance goal -- so the variable def is what really exercises
the law; and the instance still earns its place as the arithmetic check.
Laws-only counts: nat.bend 128, int.bend 32, qext.bend 34, rat.bend **223**
(128 + 32 + 63 Rat: the two new laws), qrat.bend **232** (rat's 223 + 9 QExt).

## The LT twin of the payoff, and the mirror cost one substitution table (measured)

Round five ended with a measurement and an open unit: the norm of an extension is
*indefinite* in `d`, so `1 + 2*sqrt 3` (norm -11) has no positive raw pair equal
to its norm, no `hZ` exists for the GT law, and forcing the positive spelling 11
makes the same product multiply out to -1. The unit that closes that hole is
`QExt.inv.value.lt`, the payoff stated at round four's *negative* divisor
spelling, and it is now in `src/qrat.bend` with three fills in
`src/qrat_proofs.bend`.

        x^-1 = conj(x)/norm(d,x),     norm(d,x) = a^2 - b^2*d < 0

**The statement.** Same shape as the GT law, with `ap` replaced by `bp` and the
divisor written `Rat{Rat.num(0n, 1n+bp), 1n+dp}` -- the negative spelling, i.e.
`-(1+bp)/(1+dp)` -- and `hZ` saying the norm *is* that rational. `Nat.cmp(0n, 1n+bp)`
computes to `LT{}` on constructors, so `Rat.div` against it reduces by
conversion, exactly as on the GT side. The reciprocal is the thing worth
re-reading round four for: `Rat.inv`'s LT branch is
`Rat{Rat.num(0n, d), Nat.sub(nn, np)}`, so with `np = 0n`, `nn = 1n+bp`,
`d = 1n+dp` the reciprocal is `Rat{Rat.num(0n, 1n+dp), 1n+bp}` -- the *negative*
raw shape, **not** the GT reciprocal `Rat{Rat.num(1n+dp, 0n), 1n+ap}` with a
coordinate flipped. The fill's closing law is `Rat.mul_inv.lt(0n, 1n+bp, dp, {==})`
and it only closes because of that.

**The fills are the GT fills, and the check that they are is the checker.**
Nothing in either coordinate chain is about the sign of the norm: the same
`Rat.neg_mul`, the same backwards `Rat.mul_add_left.arb`, the same congruence
against `hZ`, the same `{==}` denominator witnesses (they only need `rh`'s
denominator to be a successor, and `1n+bp` is one just as `1n+ap` is). So the LT
block was produced from the GT block by a substitution table of eleven literal
strings -- three def names, the `+ap: Nat` parameter, the two `hZ` types, the two
`rh` spellings in the goals, the two `R.Rat.of` lets, and the closing
`Rat.mul_inv.gt(1n+ap, 0n, dp, {==})` -- applied in a script, with an assertion
that every pattern occurred and a scan showing no `ap` left in the block. The GT
half of that script then had to be run *backwards*: the first attempt wrote
`head + header + transformed_block` over the file, which replaced the GT block
instead of following it, and the checker said so immediately -- `Error: 1 TODO
found`, one law short of the 233 in the laws file. Inverting the table restored
the GT block byte-for-byte, and the check that it is byte-for-byte is that the
restored file prints `All terms check.`: a rewrite chain with one wrong
identifier in it does not close. Worth recording as a technique: a mirror that is
*claimed* to be a relabelling can be produced by relabelling, and the checker is
the proof that the claim was right -- but only if the original is kept until it
checks.

**What the pair of laws covers, and what it does not.** Together they cover every
extension whose norm is non-zero, one law per sign. Norm = 0 stays uncovered, and
that is correct rather than an omission: `a^2 = b^2*d` is satisfiable for non-zero
`x` whenever `d` is a square (`x = 2 + sqrt 4 = 4` has norm 0), and an extension
whose norm is zero is a zero divisor -- there is no inverse to state. The
*branch-free* form is still out of reach for the reason round four measured: at a
variable divisor the `Nat.cmp` is stuck inside `Rat.inv`'s argument list next to
the `{==}` whose type mentions it.

**The consumer probe grew both ways.** `probe.payoff.bend` now records the
negative conversion too -- `Rat.div(a, Rat{Rat.num(0n,1n+bp),1n+dp})` unfolds by
conversion to `mul(a, Rat{Rat.num(0n,1n+dp),1n+bp})` at a variable dividend, which
is the fact the `rh` spelling rests on, stated from the caller's side -- plus
`probe.payoff.lt` (the law at a variable `x`, body a call to the published name)
and `probe.payoff.instance.lt`, the literal

    1/(1 + 2*sqrt 3) = (1 - 2*sqrt 3)/(-11)

with every hypothesis `{==}`: the norm computes to -11, which is the spelling at
`bp = 10`, `dp = 0`. That instance is the one the GT law cannot state at all, so
it is also the honest demonstration that the LT twin was needed. As with the GT
instance, at literals the product reduces on its own (`{==}` closes the goal);
what the call adds is that the published name is callable with every implicit
argument inferred.

**Counts.** Laws-only: nat.bend 128, int.bend 32, qext.bend 34, rat.bend 223,
qrat.bend **233** (rat's 223 + 10 QExt -- the LT law is the tenth). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` and
`probe.payoff.bend`, and `scratch.bend` prints the same `Rat.inv` triple it has
since round three.

## The operations QExt.inv and QExt.div, and the field axiom measured false at non-canonical spellings (measured)

Round six closed the payoff as a *relation*: `x * (conj(x)/norm(d,x)) = 1`, one
law per sign of the norm, with the norm spelled as a raw rational pair of that
sign plus `hZ` saying the norm *is* that rational. Nothing in the tree named an
inverse or a quotient as a `QExt` operation, though, so the pair had no
consumer that could write `1/x` -- it could only write the product the laws are
stated over. This round adds the operations and the two law pairs stated over
them, and measures the boundary of the field axiom.

**The defs** (in `src/qrat.bend`, right after `QExt.norm`):

    QExt.inv(x, q)      = QExt{QExt.re(x)/q, (-QExt.im(x))/q}
    QExt.div(d, x, y, q) = QExt.mul(d, x, QExt.inv(y, q))

`q` is a *parameter*, not `QExt.norm(d,x)` computed in the body. That is forced
by round four's wall, one layer up: `Rat.div` needs a constructor-headed divisor
for the `Nat.cmp` inside `Rat.inv`'s argument list to compute, and
`QExt.norm(d,x)` is an operation's output, so a computed `q` would put the stuck
comparison back where no rewrite reaches it. The caller hands over the norm as a
spelled rational (`R.Rat.of(1n+ap, 0n, dp)` or `R.Rat.of(0n, 1n+bp, dp)`), and
the laws' `hZ` is what says that rational *is* the norm. `QExt.div`'s `q` is
*y's* norm spelling -- round five's note that `QExt.inv`'s body is verbatim the
divisor expression the value laws are stated over now pays off: the operations
apply those laws by conversion alone, with no bridge.

**The linearity lesson, second instance.** The first attempt was
`def QExt.inv(x: QExt, q: R.Rat)` and it died with `expected : q / observed : q
(consumed more than once)`: `q` appears twice in the body, and `x` twice through
`re`/`im`. `+x, +q` is the fix -- the same shape as `Nat.gcd_self`'s `+a`
(round two) and `QExt.neg_neg`'s coefficient hypotheses. Worth stating as a rule
for defs rather than laws: *a parameter used twice in a body must be declared
implicit*, and an operation whose body destructures its argument twice is
automatically in that case.

**`QExt.mul_inv.gt`/`.lt`, and why there is no third law.** Each states
`QExt.mul(d, x, QExt.inv(x, spelled_norm)) = QExt.one()`, with the same `gx`/`hx`
positivity hypotheses as the value laws and the same `hZ`, and each fill is
*one call* to `QExt.inv.value.gt`/`.lt`: `QExt.inv(x, q)` unfolds to the
divisor expression those laws are stated over and `R.Rat.of` unfolds to the
spelled constructor. The pair exists so the operation and the spelled relation
cannot drift apart; if a value law is ever restated, these two are what fails.
The fill's comment says so.

`x/x = 1` is deliberately **not** a law here, and the reason is a measurement
rather than a preference: `QExt.div(d, x, x, q)` unfolds to
`QExt.mul(d, x, QExt.inv(x, q))` verbatim, which is exactly the product
`QExt.mul_inv` concludes, so a caller writes the quotient they want and cites
that law. `Rat.div_self.gt` is a real Rat law only because Rat's divisor there
is a raw coordinate spelling; at the operation level the statement collapses
into the one already present. `probe.payoff.bend` records the collapse from the
caller's side: `probe.op.div.self.gt`/`.lt` are each one call, at a variable `x`.

**`QExt.div_add.gt`/`.lt`.** `(x+y)/z = x/z + y/z`, six positivity hypotheses
(the same list `QExt.mul_distrib` takes) and -- unlike `mul_inv` -- **no `hZ`**:
the law is about dividing by the spelled rational, and what connects a spelling
to a norm is the caller's business. What makes the fill short is the asymmetry
with `QExt.mul_distrib`, which needs the *reciprocal's* coordinate positivity as
hypotheses: here it is not a hypothesis but a derivation, because the reciprocal
of a spelled rational is a constructor whose denominator is `1n+ap` (positive by
`{==}`) and `Rat.mul.den.pos` lifts the divisor's positivity to the quotient's.
So the fill is four steps: `+rp = R.Rat.of(1n+dp, 0n, ap)` (the reciprocal's raw
pair, the one `probe.unfold.div.pos` records), two `R.Rat.mul.den.pos` calls --
the second under `R.Rat.neg`, so it is fed `R.Rat.neg.den.pos(zb, hz)` -- and
then `qext.mul_add_left` at the reciprocal. The LT twin is the same with
`of(0n, 1n+bp, dp)` / `of(0n, 1n+dp, bp)`, all witnesses still `{==}`.

`qext.mul_add_left` is a bare *helper*, not a law: `QExt.mul_distrib` is stated
on the left (`(y+z)*x`), the mirror is `QExt.mul_comm` + that law + two
`QExt.mul_comm`s under a cong, and both `div_add` branches share it. The Rat
layer keeps the same mirror as a *law* (`Rat.mul_add_left.arb`) because there it
is a fact about multiplication that consumers may want; here its only consumer
is the fill, and the layer's habit is to keep bare helpers bare (as
`qext.re`/`qext.im` are).

**The `+rp` let, and a gotcha that reappeared in a new position.** The first
version wrote `+rp = R.Rat{R.Rat.num(1n+dp, 0n), 1n+ap}` and died with
`expected : an annotated term (cannot infer) / observed : rat.Rat{int.Int{1n+dp,
0n}, 1n+ap}` -- the long-recorded rule that a constructor literal cannot head a
`let`, which is the whole reason `Rat.of` exists. `R.Rat.of(1n+dp, 0n, ap)` is
the fix, in both branches.

**The field axiom `(x/y)*y = x` is out of reach, and the probes say why.** Three
measurements, in this order, each one run before any proof was attempted:

1. At a variable `x`, `QExt.mul(d, x, QExt.one()) = x` filled with `{==}` fails:
   `expected : QExt.mul(...) / observed : x`. Not definitional -- `QExt.mul`
   destructures its arguments and its coordinates are sums of products, so there
   is real work here, and `QExt.mul_one` is the law that would do it.
2. At a canonical literal instance (`x = y = 2 + sqrt 2`, `d = 2`, norm 2,
   divisor `R.Rat.of(1n+1n, 0n, 0n)`), the axiom closes with `{==}`: `All terms
   check.` So the equation is *true* -- what is missing is a proof at a variable,
   not a counterexample.
3. At a **non-canonical** dividend it is *false*: with real coordinate
   `Rat{Int{2n,0n}, 2n}` (the value 1, spelled unreduced), `x * QExt.one()`
   fails with `expected : Rat{Int{1n,0n},1n} / observed : Rat{Int{2n,0n},2n}`
   -- the product comes back normalized while `x` keeps the unreduced spelling --
   and the axiom at that dividend with `y = QExt.one()` fails the same way.

So no law can state the field axiom at arbitrary values: `==` on `Rat` is
structural and `QExt.one()`'s own coordinates are canonical, so the conclusion is
canonical whether or not the dividend is. The variable form has to be presented
over canonical spellings (canonicality hypotheses, exactly the shape
`Rat.mul_one(n, d, fx)` uses, where `fx : Rat.mk(n,d) == Rat{n,d}` is the
bridge), and it therefore waits on a presentation-level `QExt.mul_one` rather
than on any positivity fact. That is the next unit. The route is stated as a
route, not as a result: measurement 1 is what says `mul_one` is needed at all,
and the canonicality restriction is a restriction on the *proof*, since
measurement 2 shows the equation itself holds.

**The consumer probe grew the operation surface.** `probe.payoff.bend` gains
six defs (twelve in the file now, from the six of round six): `probe.op.unfold.inv` (that `QExt.inv` is its own body by conversion,
at a variable value and a variable rational), `probe.op.div.self.gt`/`.lt` (the
collapse above, one call each), `probe.op.div_add.gt`/`.lt` (the new pair at
variables), and `probe.op.instance`
(`(2 + sqrt 2)/(2 + sqrt 2) = 1` at literals -- `{==}`, as the rest of the
literal instances are). The defs are written against the published names at
their own telescopes, so an implicit argument that stops being inferable fails
here first.

**Counts, measured.** Laws-only: nat.bend 128, int.bend 32, qext.bend 34,
rat.bend 223, qrat.bend **237** (rat's 223 + 14 QExt: the ten of round six, the
two `mul_inv` operation laws, the two `div_add` operation laws). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` and
`probe.payoff.bend`; `scratch.bend` prints the same triple it has since round
three. The defs themselves do not move the count -- laws-only was still 233
after `QExt.inv` and `QExt.div` were added, and `qrat_proofs.bend` checked
immediately.

## QExt.mul_one and the field axiom on both signs: the canonical presentation is part of the statement (measured)

Round seven measured the field axiom `(x/y)*y = x` out of reach and named the
reason: every route passes through `x * 1 = x`, which is false at non-canonical
dividends, so the axiom waits on a presentation-level `QExt.mul_one`. This round
adds that law and then the axiom itself, one law per sign of the norm.

**`QExt.mul_one` is stated over bridges, not over coprimality.**

    law QExt.mul_one:
      for +d, np, nn, dp, mq, mn, dq
      for +f1: {Rat.mk(Rat.num(np,nn), 1n+dp) = Rat{Rat.num(np,nn), 1n+dp}}
      for +f2: {Rat.mk(Rat.num(mq,mn), 1n+dq) = Rat{Rat.num(mq,mn), 1n+dq}}
      {QExt.mul(d, QExt.of(np,nn,dp,mq,mn,dq), QExt.one()) = QExt.of(np,nn,dp,mq,mn,dq)}

The two bridges are exactly `Rat.mul_one`'s own hypothesis, so the law passes
them straight through instead of re-deriving them; a bridge is strictly weaker
than coprimality, and a `neg_neg`-style caller who *has* coprimality reaches
these with one `Rat.mk.fixed` call per coordinate and nothing new to prove
(`probe.mul_one.fixed` is that caller, written out). The `QExt.of` spelling is
the same canonical presentation `QExt.neg_neg` and `QExt.add_assoc` use.

**The real coordinate is where the work is, and it is the radicand's fault.**
`QExt.nat(d) = Rat{Rat.num(d,0n), 1n}` has base denominator `1n`, while
`Rat.mul_zero` is stated at `Rat{n, 1n+dp}` -- there is no way to feed the
radicand's coefficient to it. So the file gains one bare helper,
`qext.nat.mul_zero`, the same move `qext.re`/`qext.im` make: a fact about a
narrow spelling that only a fill consumes stays a helper. With it, the real
coordinate is four steps (`mul_zero` on the imaginary product, `qext.nat.mul_zero`
on the radicand term, `Rat.mul_one` on the surviving product, `Rat.add_zero` at
the end) and the imaginary coordinate is three (`mul_zero`, `Rat.mul_one`,
`Rat.zero_add`); the composing fill is two `qext.re`/`qext.im` trans steps. The
law's own left-hand side reduces to `QExt{Lr, Li}` after `match x`, so no
bridging step is needed at the top -- the same fact the payoff laws rest on.

**Four probes ran before any of it was written**, on the pattern that has worked
since round two -- one file per question, each a deliberately-false `{==}` whose
error prints both endpoints in full SNF:

- the real coordinate of `QExt.mul(d, x, QExt.one())` at a canonical
  `x = QExt{Rat{n1,1n+p1}, Rat{n2,1n+p2}}` is
  `Rat.add(Rat.mk(Int.mul(n1, Int{1n,0n}), 1n+Nat.mul(p1,1n)),
   Rat.mul(QExt.nat(d), Rat.mk(Int.mul(n2, Int{0n,0n}), 1n+Nat.mul(p2,1n))))`
  -- the first summand already `mk`-headed, the second still `mul`-headed with
  the radicand factor *unfolded*. Writing the intermediates in this spelling,
  rather than in the `Rat.mul(XA, one())` spelling one would expect, is what made
  the fill short.
- `Rat.add(Rat{n,1n+p}, zero)` reduces to
  `mk(Int.add(Int.mul(n, Int{1n,0n}), Int{0n,0n}), 1n+Nat.mul(p,1n))` -- exactly
  `Rat.add_zero`'s `fx` input, so that law applies with `{==}` for its bridge.
- `Rat.mul(Rat{n,1n+p}, zero)` and `Rat.mul(Rat{n,1n+p}, one)` likewise reduce to
  exactly `Rat.mul_zero`'s and `Rat.mul_one`'s inputs.
- `Rat.mk(Int.zero(), 1n)` is `Rat.zero()` by conversion, and `Nat.mul(1n,1n)` is
  `1n` -- the base cases the fills lean on.

**One failure with no location line, diagnosed by bisection rather than by
reading.** The first version of the fill failed with an error whose text was
65537 bytes of one unfolded `Rat.mk` normalization -- `Nat.divmod`/`gcd` towers
over `Nat.sub(np,nn)`, `Nat.sub(mq,mn)`, `Nat.sub(0n,d)`, `Nat.mul(1n+dq,1n)`.
`grep -c 'Location'` over the capture returned **0**: a giant-term error has no
location line at all, so "read the head of the error" is not available and
`head -30` lands mid-term (lines are enormous). What worked was a three-way
bisection written as a script: back the file up, extract the new block, and
rebuild the file keeping any subset of the three pieces -- `.re` alone, `.im`
alone, the composing fill alone -- running the gate on each. `im` alone checked
(`Error: 1 TODO found.`, the unfilled law); the fill alone failed with
`expected : a defined name / observed : QExt.mul_one.re` (it calls a def that
isn't there); `re` alone produced the giant term. That named the culprit in three
runs without reading a byte of the 64 KB. A botched python edit in the middle of
this produced a parse error at lines 979-981 and was fixed by restoring the
backup wholesale -- **full restore, then patch**, never incremental repair of a
mangled edit.

**Two bugs in the real coordinate, both about the endpoint a rewrite meets.**

1. `+e1` was the *sub-term* equality `mul(D, mul(XB, zero)) = mul(D, zero)` fed
   to a `Equal.trans` whose endpoints were the whole sums. Fix: wrap it, i.e.
   make e1 an outer `Equal.cong` over `u => Rat.add(Rat.mul(XA, one()), u)` whose
   evidence is that inner `cong`. (The checker's first complaint, after the
   wrapping, moved up a level -- which is itself the signal that the level was
   wrong.)
2. In the composing fill, `Equal.trans`'s middle term was `QExt{A1, B1}` -- the
   chain's internal intermediate name -- but the first leg concludes at
   `QExt{XA, B1}`, the rewritten coordinate. `trans`'s `b` is the term both legs
   must *meet* at; it is not a name of convenience. This is the second time this
   exact mistake appeared (round three, `QExt{A1,B1}` → `QExt{XA,B1}` in the
   payoff's compose), so it is worth a rule: **write `trans`'s middle term as the
   exact endpoint of the first leg, copying it out of the first leg's evidence,
   not out of the chain's list of names.**

**The field axiom, `QExt.div_mul_cancel.gt`/`.lt`.** `(x/y)*y = x` with a
canonical dividend, one law per sign of the norm's spelling. Three deliberate
choices, each measured rather than preferred:

- `x` is canonical (the `QExt.of` spelling plus `mul_one`'s two bridges). Nothing
  branch-free can exist: `==` on `QExt` is structural and the product comes back
  normalized, which is round seven's measurement 3 and the reason `QExt.mul_one`
  had to be stated this way in the first place.
- `x`'s positivity is **not** a hypothesis, though `mul_assoc` needs it: the
  spelled `x` has successor denominators, so `Nat.cmp(0n, 1n+dp)` computes and the
  fill passes `{==}` -- the same derivation-not-hypothesis move `div_add`'s fill
  makes.
- `y` is arbitrary, so both of its coordinates' positivity and the spelled norm
  with `hZ` are hypotheses -- exactly what `QExt.mul_inv` asks for, because the
  fill ends by calling it.

The fill is the composition the design was waiting for: `QExt.div` unfolds to
`mul(d, x, inv(y,q))` by definition; `mul_assoc` regroups it to
`mul(d, x, mul(d, inv(y,q), y))`; one `cong` with `mul_comm` inside moves the
reciprocal to the right; one `cong` with `QExt.mul_inv.gt` (which states
`y * inv(y) = one()`, hence the `mul_comm` *first* -- assoc leaves `inv(y) * y`)
collapses the pair; and `QExt.mul_one` finishes. Five lets, three derived
positivity facts, no new helper. The three bugs hit while writing it, in order:

1. `+Y = Q.QExt{ya, yb}` -- the constructor-cannot-head-a-`let` rule, fourth
   instance in this project. The fix here was not `QExt.of` but deletion: the
   `match y` binder already exists, so use `y` itself.
2. `gi`/`hi` were built from `x`'s coordinates with `{==}`. They are the
   *reciprocal's* positivity, so they must come from `y`:
   `Rat.mul.den.pos(ya, rp, gy, {==})` and
   `Rat.mul.den.pos(Rat.neg(yb), rp, Rat.neg.den.pos(yb, hy), {==})`. The error
   printed the type it wanted, `{Nat.cmp(0n, denof(mul(ya, rp))) == LT{}}`, which
   named the operand.
3. The giant mismatch (expected and observed both 2614 characters, first
   difference at character 1530, pure `mul`-grouping with no spelling
   difference): the outer `Equal.trans`'s middle term was `L2`, but its legs
   prove `{L1 = L3}` and `{L3 = X}` -- it had to be `L1, L3, X`. Same rule as
   above, one level out.

**Localizing a 2614-character term diff, and reading `base.bend` instead of
guessing.** Two cheap techniques carried bug 3: (a) a token-level `difflib`
diff, tokenizing on `mul(|add(|neg(|{,|},|,` plus words, so the opcodes say
whether the difference is grouping or spelling -- here every opcode was
`mul`-grouping, which ruled out the whole class of spelling bugs in one step;
(b) replacing a single evidence term with `{==}` so the checker prints the type
it *demands* at that position (that is how bug 2's wanted type was read, and how
the `mul(mul(ya,q),ya)` vs `mul(ya,mul(ya,q))` orientation was settled). And
`base.bend:355-396` gives the three `Equal` fills exactly: `cong(A,B,f,a,b,e)`
fills `%e : {f(a) = f(_)}` with `{==}`, `sym(A,a,b,e)` fills `%e : {_ = a}` with
`{==}`, and `trans(A,a,b,c,ab,bc)` fills `%bc : {a = _}` with `ab` -- so `b` is
the shared middle term and nothing else.

**The LT twin was generated, not written.** Five substitutions on the GT def text
(`.gt(` → `.lt(`, the parameter list, the two `R.Rat.of(...)` spellings, the
closing `QExt.mul_inv` call), each applied with an assertion and a printed count
(all ×1), followed by a scan for leftovers (`1n+ap`, `, ap,`, `mul_inv.gt`),
then appended as `gt_text + "\n" + lt_text`. It checked on the first run. Round
six's lesson repeats: a mirror *claimed* to be a relabelling can be produced by
relabelling, and the checker is the proof the claim was right -- which held here
only because the GT text was still in the file. (In round six the first script
overwrote the original instead of following it, and the checker caught it as a
missing TODO.)

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat 223, qrat.bend
**240** = 128 Nat + 32 Int + 63 Rat + **17 QExt** (the ten of round six, the four
operation laws of round seven, `QExt.mul_one`, and the two `div_mul_cancel`
laws). All five `src/*_proofs.bend` print `All terms check.`, as do
`probe.bend` and `probe.payoff.bend`; `scratch.bend` prints the same triple it
has since round three. `probe.payoff.bend` grew from the twelve defs of the last
commit to eighteen -- three for `QExt.mul_one`, then `probe.div_mul_cancel.gt`/`.lt` from the caller's side at a variable `y`, and
`probe.div_mul_cancel.instance`, `1/(2 + sqrt 2) * (2 + sqrt 2) = 1` at literals,
where every hypothesis is `{==}` and -- as with `probe.mul_one.instance` -- the
product also reduces on its own, so the instance is the arithmetic check and the
variable defs are what exercise the law.

**Temp probes, deleted.** The five scratch probe files this round needed
(`probe.field.a.bend` through `probe.field.d.bend`, `probe.mulone.bend`) were
removed before the commit; their measurements are the four bullets above.

## The additive identity and inverse: the last three laws, and the shortest fills in the layer (measured)

Round eight closed the multiplicative side of the operation surface. What was
left was the additive group: `QExt.add_comm`, `add_assoc`, `sub_eq_add_neg` and
`neg_neg` were in, but nothing said `x + 0 = x` or `x + (-x) = 0` -- and the Rat
layer has all of them (`Rat.add_zero`, `Rat.zero_add`, `Rat.add_neg`). This round
adds the three, and they are the cheapest laws in the layer.

**The additive identity is false at an unreduced coordinate, measured before the
comment was written.** The probe is round seven's, one operation over: at the
real coordinate `Rat{Int{2,0}, 2}`,

    QExt.add(QExt{Rat{Int{2,0},2}, Rat.zero()}, QExt.zero())

comes back `QExt{Rat{Int{1,0},1}, Rat{Int{0,0},1}}` -- the expected/observed pair
the checker printed, with a location line this time (the term is small). So
`QExt.add_zero`/`zero_add` are stated at the canonical presentation with
`QExt.mul_one`'s two bridges, for `QExt.mul_one`'s reason: `==` on `QExt` is
structural, and a non-canonical `x` does not survive the sum.

**What makes them short, and what they do not need.** `QExt.add` is
componentwise, so after the coordinates are read each coordinate goal *is* the Rat
law's statement -- `Rat.add(Rat{n, 1n+dp}, Rat.zero())` against
`Rat{n, 1n+dp}` -- with nothing in between and no intermediate term to name:
one `R.Rat.add_zero(n, 1n+dp, fx)` call per coordinate, and a composing fill that
is just the two `qext.re`/`qext.im` witnesses. In particular there is no radicand
coefficient anywhere, so no helper is needed: `qext.nat.mul_zero` exists only
because `QExt.mul`'s real coordinate multiplies by `QExt.nat(d)`, whose
denominator is base 1 and therefore unreachable by `Rat.mul_zero`. That is also
why these two laws take no `d` parameter: the radicand is `QExt.mul`'s parameter,
not `QExt.add`'s.

**`QExt.add_neg` is stated at an arbitrary value, and that is a contrast worth
recording.** `Rat.add_neg` needs only a coefficient and its denominator's
positivity, and its conclusion is `Rat.zero()` on the nose -- unlike `Rat.neg_neg`
and `Rat.mul_one`, which compare an `mk` against a constructor and therefore need
coprimality or a bridge. Negation is componentwise and produces no `mk` of its
own, so the two sides of the coordinate equation are both compositions and `==`
compares them directly. The fill is one `R.Rat.add_neg` per coordinate, at a
variable `x`, inside a `match`; the law's positivity hypotheses arrive intact
because `QExt.re(QExt{xa,xb})` reduces to `xa` after the match.

**There is deliberately no `QExt.neg_add`, and the reason is a naming fact
rather than a mathematical one.** In this tree `Rat.neg_add` (rat.bend:1206) is
the *distribution* law `-(x + y) = (-x) + (-y)`, not the flipped inverse. A QExt
law called `neg_add` stating `(-x) + x = 0` would therefore mean something
different from its Rat namesake, and the flipped inverse is two steps any caller
can take -- `QExt.add_comm` then `QExt.add_neg` -- so nothing in the tree states
it. (`Rat` itself has no flipped form either. The two layers now agree on
`add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg`, `neg_neg` and
`sub_eq_add_neg`; what `QExt` still lacks on the additive side is `Rat.neg_add`
itself -- negation distributing over a sum -- and on the multiplicative side the
pair `Rat.mul_neg`/`Rat.neg_mul`. Those three are laws about how `neg` interacts
with the operations rather than about the identity elements, and they are the
natural next unit on this side if the structure is to be mirrored exactly.)

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat 223, qrat.bend
**243** = 128 Nat + 32 Int + 63 Rat + **20 QExt** (the seventeen of rounds six to
eight plus these three). All five `src/*_proofs.bend` print `All terms check.`,
as do `probe.bend` and `probe.payoff.bend`; `scratch.bend` prints the same triple
it has since round three. `probe.payoff.bend` grew from eighteen defs to
twenty-three: `probe.add_zero`, `probe.zero_add` and `probe.add_neg` from the
caller's side at variables, `probe.add_neg.sub_self` (`x - x = 0` written with
`QExt.sub`, which the law reaches by conversion -- the shape a caller writing a
difference actually has), and `probe.add_zero.instance` (`(2 + sqrt 2) + 0`,
`{==}`, as with the other literal instances).

**All three fills checked on the first run**, which is worth noting against the
record of the last two rounds: every step here was a law applied at a spelling the
goal already carried, with no intermediate term, no congruence to place and no
`trans` middle to match up. The two rounds before this one each cost several
iterations on exactly those three things.

## The negation and conjugation block: a rung-2 Rat law was the missing rung, and one law is out of reach (measured)

Round nine closed the operation surface and named the next unit itself: what the
`QExt` layer still lacked was "`Rat.neg_add` itself -- negation distributing over a
sum -- and on the multiplicative side the pair `Rat.mul_neg`/`Rat.neg_mul`". This
round adds those, plus the two conjugation laws that finish the additive half of
`conj`, and the round needed a *new Rat law* to do it. It also found that one of
the round-nine sentences about a law name was about the wrong law, and that one
member of the block -- `conj(x*y) = conj(x)*conj(y)` -- cannot be stated here at
all.

**The canonical `Rat.neg_add` cannot reach an operation output, so the rung-2 form
had to be written.** `Rat.neg_add` (rat.bend:1206) spells its summands
`Rat{num(np,nn), 1n+dp}`; `QExt.neg_add`'s summands are coordinates of an arbitrary
`QExt`, which after `QExt.add` are `Int.add`-headed sums of scaled difference
pairs, and no congruence turns one into the other. This is the fourth time the same
pattern has forced a rung-2 law (`Rat.add_assoc.arb`, `Rat.mul_assoc.arb`,
`Rat.mul_distrib.arb`, now `Rat.neg_add.arb`): the *canonical* Rat laws are what the
`Rat` layer is stated over, and the *arbitrary-value* forms are what a composing
layer can call. `Rat.neg_add.arb` (rat.bend:1360) is

    -(x + y) = (-x) + (-y)      for arbitrary x, y, with only px and py

-- the −1 factor written as `Rat.neg(Rat.one())`, which is `neg_eq_mul_negone`'s own
spelling of it, so its positivity is `{==}` at a literal and no hypothesis is
needed for it. The route is `Rat.neg_eq_mul_negone` (negation is multiplication by
−1), `Rat.mul_distrib.arb`, and then the same law again at each summand under a
congruence. No destructuring, no value law, no cross product. The fill
(rat_proofs.bend:4559) is a three-deep `Equal.trans` whose middle terms are the
scaled summands; it mirrors `Rat.neg_mul`'s three-step fill one operation over.

**The one error in that fill is a rule about `Equal.sym` worth stating.** The first
leg is `Rat.neg_eq_mul_negone(s)` and the goal's left endpoint is already
`neg(s)`, so the law applies in the direction the `trans` needs and must be cited
*naked*. Wrapping it in `Equal.sym` produced the flip the checker printed --
`expected {neg(s) == mul(A,s)}` against `observed {mul(A,s) == neg(s)}`. `sym`
belongs on the *small congruence witnesses* inside the last leg (which need the
opposite orientation from what `neg_eq_mul_negone` states), not on the leg that
already matches. Both are visible in the fill as two `Equal.sym`s on the inner
witnesses and none on the leg.

**`QExt.neg_add`'s hypothesis set was wrong in the first draft, and reading the
definition is what fixed it.** The draft took only the *imaginary* coefficients'
positivity, on the assumption that `QExt.neg` negates the imaginary coordinate
alone. It does not:

    QExt.neg(x) = QExt{Rat.neg(xa), Rat.neg(xb)}

-- componentwise. Negating the imaginary coefficient alone is `QExt.conj`. So both
coordinates are negated sums needing both summands' positivity, and the law
(qrat.bend:484) takes `gx, gy, hx, hy`. The fill (qrat_proofs.bend:1109) is then
two `Rat.neg_add.arb` calls -- one per coordinate, via `qext.re`/`qext.im` -- and
nothing else, with no congruence anywhere, because both sides of each coordinate
equation are compositions `==` compares directly. The general lesson: the
hypothesis list of a composing law is what the *fill's* Rat laws need, so deriving
it from the fill (or from the operation's definition) before writing the statement
costs less than a rewrite after.

**The multiplicative twins, and what they cost.** `QExt.mul_neg` and
`QExt.neg_mul` (`mul(d,x,-y) = -(mul(d,x,y))` and `mul(d,-x,y) = -(mul(d,x,y))`,
qrat.bend:503 and :513) are not symmetric in price. `mul_neg` is per coordinate and
needs a helper level: a coordinate of a product is a sum of two products, so the
negation has to travel one factor at a time (`Rat.mul_neg` at each product of
`xa`/`ya`, and on the real coordinate if the radicand term is involved,
`Rat.mul.den.pos(xb, yb, hx, hy)` as the positivity prototype for the coefficient
`d` pulled inside the negation under a congruence), and then the two negations
merge with `Equal.sym(Rat.neg_add.arb(P, Q, ...))` -- the law above it, read
backwards. `QExt.neg_mul` is then *three steps and no coordinates of its own*:
`QExt.mul_comm` moves the negation into the second slot, `QExt.mul_neg` does the
work, and one `Equal.cong` of `QExt.neg` over `QExt.mul_comm` swaps the factor
back. Two laws for the price of one because the commuting law was already in the
file.

**`conj_add` is one call, `conj_conj` is one call plus a hypothesis, and together
they say `conj` is an additive automorphism.** `QExt.conj_add` (qrat.bend:341)
needs a single `Rat.neg_add.arb` on the imaginary coordinate and no congruence at
all: the real coordinate is the *same term* on both sides, and addition is
componentwise. `QExt.conj_conj` (qrat.bend:373) is `neg(neg(im x)) = im x`, so it
needs `Rat.neg_neg`, which is false unconditionally (rat.bend records the witness
`np = 4, nn = 0, dp = 1`) and therefore carries the canonical spelling plus
coprimality -- on the imaginary coordinate *only*, because the real coordinate
never enters it. Its fill (qrat_proofs.bend:1267) is the `Q.QExt.neg_neg` call
shape one operation over. One error here, and it is the constructor-in-a-`let`
rule again: `+RE = R.Rat{R.Rat.num(np,nn), 1n+dp}` is rejected with "an annotated
term (cannot infer)", and `R.Rat.of(np, nn, dp)` is the fix -- a bare constructor
cannot be the right-hand side of a `let` in this checker.

**`conj(x*y) = conj(x)*conj(y)` is out of reach here, and not for a presentation
reason.** Its real coordinate is `mul(xa,ya) + d*mul(neg xb, neg yb)` against
`mul(xa,ya) + d*mul(xb,yb)`, so the law needs

    mul(neg xb, neg yb) = mul(xb, yb)     at variables

and the Rat laws reach it by neither of the two routes they offer -- both end at a
law whose statement a *stuck product* cannot satisfy. Route one is double negation
at the product's own output, `neg(neg(mul(xb,yb))) = mul(xb,yb)`: `Rat.neg_neg`
(rat.bend:813) concludes a constructor-headed `Rat{...}`, while applications of
`Rat.mul` at variables are def-headed and stuck. Route two is multiplying by −1
twice (`Rat.neg_eq_mul_negone`, both halves unconditional), associating to
`mul(mul(-1,-1), U)`, and closing with `mul(Rat.one(), U) = U` -- which is
`Rat.one_mul` (rat.bend:293), stated over `Rat{n,d}` with a bridge hypothesis, and
so equally unable to take a stuck product. Measured this round, both closing steps
at variables, plus the literal instance that shows the identity itself is true:

    {==} at variables:  expected  neg(neg(mul(a,b)))        observed  mul(a,b)   (fails)
    {==} at variables:  expected  mul(one(), mul(a,b))      observed  mul(a,b)   (fails)
    {==} at literals:   neg(neg(mul(Rat{Int{2,0},3}, Rat{Int{5,0},7})))
                          = mul(Rat{Int{2,0},3}, Rat{Int{5,0},7})   (closes)

-- the identity is *true* and every literal instance is `{==}`, while at variables
the checker cannot even compare the two sides. (This is an argument over the law
inventory, not an induction over all chains: what is measured is that both closing
steps fail, and what is reasoned is that the permutational laws -- `mul_comm`,
`mul_assoc.arb`, `mul_neg`, `neg_mul` -- only ever move a negation to the outside
or remove one, so they cannot produce the missing double negation at a product.) What would unblock it is a Rat law
about `mk`'s own output being reduced: the coprimality of the numerator and
denominator that `mk` produces, which is Nat-level gcd work rather than a
rearrangement. Until then the law is deliberately absent, and the exclusion, this
route and both measurements are recorded in `QExt.conj_conj`'s comment where a
reader looking for the missing law will actually be.

**Counts, measured.** Laws-only: nat 128, int 32, qext 34, rat **224**, qrat.bend
**249** = 128 Nat + 32 Int + **64 Rat** + **25 QExt** (the twenty of rounds six to
nine plus `neg_add`, `mul_neg`, `neg_mul`, `conj_add`, `conj_conj`). All five
`src/*_proofs.bend` print `All terms check.`, as do `probe.bend` (restored verbatim
from HEAD and re-checked after a stray experiment was found in it) and
`probe.payoff.bend`; `scratch.bend` prints the same triple it has since round
three. `probe.payoff.bend` grew from twenty-three defs to **thirty**: the five laws
from the caller's side at variables, `probe.neg_add.out` (the same law through
`Equal.sym`, because the orientation a caller with a sum of negations needs is not
baked into the statement), and `probe.conj_conj.instance` at literals.

**The fills reported green after one real error** (the constructor in a `let`
above) and one editing miss, which is the cheapest this layer has been since round
nine -- and the block landed in the order round nine predicted for the Rat-facing
part, with the addition round nine did not predict: that the Rat-facing part needed
`Rat.neg_add.arb` before `QExt.neg_add` could exist at all.

## The law that was out of reach a round ago landed, and the Nat work was already there (measured)

Round ten closed the negation and conjugation block with five laws and recorded
`QExt.conj_mul` as out of reach -- not unproved but unreachable at the law
inventory it had, because its real coordinate needs `mul(neg a, neg b) = mul(a, b)`
at variables and both routes to that identity died on a canonical-spelling law
(`Rat.neg_neg` concludes a constructor-headed `Rat{...}` while `Rat.mul`
applications are def-headed, so `{==}` closes the identity at literals and reports
`expected neg(neg(mul(a,b)))` / `observed mul(a,b)` at variables). The roadmap
paragraph that recorded the exclusion named the unblock as "a Rat law about the
coprimality of what `mk` produces -- Nat-level gcd work, not a rearrangement".

That law is what landed, and the round's one surprise is that the Nat work already
existed: the unblock is a rearrangement after all, at the one presentation where a
rearrangement is available.

**The two Rat laws.** `Rat.neg.reduced` (rat.bend:1381) is the rung-2 twin of the
canonical `Rat.neg_neg`: `neg(Rat{num(np,nn), 1+dp}) == Rat{num(nn,np), 1+dp}`
under `g1 : gcd(mag(np,nn), 1+dp) == 1`, and its fill is one call --
`R.Rat.mk.fixed(Nat.cmp(nn,np), nn, np, dp, {==}, g1s)` (rat_proofs.bend:4591).
`neg` of a constructor unfolds to `mk(Rat.num(nn,np), 1+dp)` definitionally and at
a coprime pair mk's output *is* the flipped spelling, so the only work is the `g1`
the caller gives and `g1s`, the mag-symmetry trans `Rat.neg_neg`'s own fill
already uses verbatim (a congruence under `gcd(., d)` fed by
`N.add_comm(sub(nn,np), sub(np,nn))`).

`Rat.mul.neg_neg.reduced` (rat.bend:1403) is the identity the QExt half was
actually missing: `mul(neg X, neg Y) = mul(X, Y)` for spelled X, Y with coprime
coordinates -- and it is **false** without them. Measured with a deliberately-false
`{==}` at the unreduced pair, `Rat.neg(Rat{Rat.num(4n,0n), 2n})` against
`Rat{Rat.num(0n,4n), 2n}`: expected `Rat{Int{0,2},1}`, observed `Rat{Int{0,4},2}`.
The left side goes through mk, which cancels the common factor; the right is a raw
spelling. The coprimality hypothesis is therefore part of the statement rather than
a convenience, and the law's comment carries the witness.

Its fill (rat_proofs.bend:4612) is the `Rat.neg_neg` template at the reduced
presentation: two congruences applying `Rat.neg.reduced` to each factor, then an
inner trans `mul(nx,ny) -> mk(num(nn,np)*num(mn,mq), mul(d,e)) -> mul(x,y)` whose
first leg is `{==}` -- mul of two constructor factors *is* the mk of the cross
product definitionally -- and whose second leg is a congruence fed by an `Int`
identity: two `Int.neg_mul` steps, two `Int.mul_comm` steps and one
`Int.neg_invol`, all of them unconditional. The coprime spelling is hypothesis, not
work: the fill consumes no Nat fact beyond the `g1`/`g2` that `Rat.neg.reduced`
already spends.

**The leg order cost one giant-term error, and its diagnosis is worth keeping.** I
had the congruence first and `{==}` second. The checker dumped both sides' SNF --
about 1.4k tokens each, single-line, no newlines -- and a token-level diff pinned
the first difference at token 730, in the `Nat.sub(nn,np)` / `Nat.sub(np,nn)`
region; the definitional fact above then explained it. Two notes for next time: the
dump has no `Location` line, so there is no position to navigate to and only a
structural comparison helps; and a line-oriented diff of it is useless, because
there are no lines.

**`QExt.conj_mul`** (qrat.bend:404) is then stated at `QExt.of`'s six coordinates
with the two imaginary coefficients' coprimality (`h1`, `h2`) and no other
hypothesis. The real coordinates need nothing: they meet inside `Rat.add`, whose own
normalization absorbs whatever spelling they carry, and `Rat.neg.reduced`'s own
hypothesis is spent inside the one Rat law. The fill is the one-call-per-coordinate
shape round ten predicted -- real: one `Rat.mul.neg_neg.reduced` under the radicand
congruence; imaginary: the same `neg_add.arb`/`mul_neg`/`neg_mul` chain
`QExt.neg_add` and `QExt.mul_neg` use, over products rather than spelled pairs.

**Two orientation facts, both measured this round.**

1. `Rat.mul.neg_neg.reduced` is stated negation-first, so the congruence that
   consumes it inside `QExt.conj_mul`'s real coordinate has to wrap it in
   `Equal.sym`: the raw call has type `{neg-side == positive-side}` while the cong
   slot wants `{positive-side == neg-side}`, and the checker reports the mismatch by
   printing the two whole `Rat` terms as expected and observed. Round ten's rule
   ("cite the first leg naked; `sym` only on the inner witnesses that need the
   opposite orientation") has a twin: a *law* cited into a congruence is naked only
   when the law's own orientation matches the congruence's direction.
2. `Equal.cong`'s `(a, b)` order is the order its evidence must have; the
   `qext.re`/`qext.im` helpers in qrat_proofs.bend fix it in place --
   `cong(f, a, b, e)` with `e : {a == b}` yields `{f(a) == f(b)}`.

**A parse error that reads like a grammar restriction and is not one.** The law's
conclusion first came out with the right-hand side missing one `)` before
`: QExt}`. The report was `expected : a term` / `observed : ':'`, pointing at the
annotation's colon -- the symptom, not the missing separator, and at the last line
of the statement rather than the line where the imbalance starts. Two round trips
went into suspecting the multi-line braced conclusion, which is not the problem:
`QExt.inv.value.gt` and `QExt.mul_one` both break lines inside `QExt.mul(...)`
argument lists and inside `QExt{...}`. The general fix is to count parentheses per
side with python before re-running, and to read "expected a term, observed `:`" as
"an argument list is still open".

**One namespace fact, measured by error.** In qrat_proofs.bend the prefix `Q.` names
both qrat.bend and the proofs module's own definitions, while `R.` is rat.bend.
Writing `R.QExt.nat(d)` in the new fill produced `expected : a defined name` /
`observed : R.QExt.nat` -- three references to fix. It is round six's cross-file
rule pointing the other way.

**Status.** Five `src/*_proofs.bend` print `All terms check.`, as do `probe.bend`
and `probe.payoff.bend`, which grew from thirty defs to **thirty-two**: the new law
from the caller's side at its own presentation, and `probe.conj_mul.instance` at
literals (1 + sqrt(2) over radicand 2, both operands `Rat{Int{1,0},1+1}`), where
both coprimality gcds compute and both pieces of evidence are `{==}`.
`scratch.bend` is unchanged. Law counts, transitive over imports: nat 128, int 32,
qext 34, rat **226** (+2: the two reduced laws), qrat.bend **252** (+3: the same two
plus `QExt.conj_mul`, so the file's own QExt inventory is 26). What is still open on
this side is the *norm*: `norm(d, x*y) = norm(d,x) * norm(d,y)`, the structure fact
that "no zero divisors when the norm is non-zero" needs.

## The norm is multiplicative: the statement had to be rewritten for the checker, and one match made the fill cheap (measured)

The goal this round was `norm(d, x*y) = norm(d,x) * norm(d,y)`, the structure fact
that "no zero divisors when the norm is non-zero" needs. It is landed, as
`QExt.norm.mul` in qrat.bend filled by `Q.QExt.norm.mul` in qrat_proofs.bend --
but not in the form it was first stated in, and the reason is a checker
measurement rather than a mathematical one.

**The rule this round was written under.** Checking is to stay under a second, and
anything that takes longer is to be done some other way. Two measurements had
already made that sharp: a `{==}` on the Rat-level spelling of this identity
(twelve spelled coordinates, each norm written out) exhausted a 4 GB heap in 41 s,
and a first fill at that presentation was killed past four minutes with no output
at all (`node --max-old-space-size=6000`). Spelling x and y as canonical `Rat`
pairs makes every norm a `Rat.sub`/`Rat.mul` expression over canonical
coefficients, and then every conversion question in the file normalizes an `mk`
chain.

**The statement.** The law is an equation of *QExt* values, not of `Rat`s:

    QExt{nxy, 0} == QExt.mul(d, QExt{nx, 0}, QExt{ny, 0})

because the Rat-level spelling is one zero-elimination away -- the product of the
two embedded norms has real coordinate `add(mul(nx,ny), mul(QExt.nat(d),
mul(zero,zero)))`, and nothing in the tree removes that second summand: there is
no `Rat.add_zero.arb` (the canonical `Rat.add_zero` is stated over `Rat{n,d}` and
needs its bridge, which is the same wall `Rat.neg_add.arb` was added to get past in
round ten).

**The stuck-term presentation.** x and y are arbitrary, so `QExt.mul(d,x,y)` does
not reduce, and every term in the law and in the fill is a stuck term:

  - the three norms are *named* by hypotheses (`hnx : nx == QExt.norm(d,x)`, and
    `hny`/`hnxy`) instead of written out;
  - the product's own coordinates' positivity arrives as `gxy`/`hxy`, because
    `QExt.re(QExt.mul(d,x,y))` is stuck and no law reaches it;
  - the `conj_mul` instance arrives as `hc`, since conj is multiplicative only at
    a reduced pair and an arbitrary x has no such fact.

**The fill, and the four errors.** Five legs:

  1. `QExt{nxy,0} -> QExt{norm(d,XY),0} -> XY*conj(XY)` -- `hnxy` under a
     congruence, then `QExt.mul_conj` read backwards;
  2. `XY*conj(XY) -> XY*(conj x * conj y)` -- `hc` under a congruence;
  3. `... -> (x*conj x)*(y*conj y)` -- `QExt.mul_assoc` four times and
     `QExt.mul_comm` once (associate left, commute y past conj x, associate back);
  4. `... -> (norm x + 0)(norm y + 0)` -- `QExt.mul_conj` twice, one congruence
     each;
  5. `... -> (nx + 0)(ny + 0)` -- `hnx`/`hny` under congruences.

Four failures on the way, each a distinct checker fact:

  - `let E1 = QExt{NX, R.Rat.zero()}` with `NX = QExt.norm(d,x)` gives
    `expected : an annotated term (cannot infer)`. A bare constructor cannot infer
    its type arguments when the argument is an operation's output rather than a
    variable -- exactly what `Rat.of` and `QExt.of` exist for. The fix is a third
    entry in that family, `QExt.emb(r) = QExt{r, R.Rat.zero()}`, a def with a
    declared return type. It adds no law: qext.bend stays at 34.
  - A positivity slot of `QExt.mul_assoc` at the argument `QExt.mul(d, y,
    QExt.conj(y))` gives expected `{Nat.cmp(0n, denof(re(mul(d,y,conj y)))) ==
    LT{}}` against observed `{Nat.cmp(0n, denof(add(mul(re y,re y), mul(nat d,
    mul(im y, neg(im y)))))) == LT{}}`. The slot's type is `denof(re(z))` with z
    the argument *as passed*, so at a stuck argument it does not reduce -- and no
    `Rat.mul.den.pos` witness can inhabit it, because those conclude the
    written-out product. Passing the argument as a spelled `QExt.pair(A,B)` makes
    the slot reduce to the witness's own spelling; that is the round's second
    constructor-inference failure, and `QExt.pair` was its first fix.
  - With the arguments spelled, the *law's* conclusion still did not line up:
    expected `M(d, CX, <spelled>)` against observed `M(d, CX, M(d,y,CY))`. The
    law's own statement keeps the nested `mul`, so a trans endpoint written as the
    reduced value is a different term.
  - The fix for both is `match x y:` with `case Q.QExt{xa, xb} Q.QExt{ya, yb}:` at
    the top of the fill. A single-constructor match refines the context, so every
    projection of x and y and every `QExt.mul` at them reduces; the spelled lets
    and `QExt.pair` then became unnecessary and were removed. This is the
    technique the existing QExt fills use -- `Q.QExt.mul_assoc`, `.mul_distrib`,
    `.mul_comm` and the rest open with a `match` -- and the round's real lesson is
    that the first two attempts were written *without* it, at terms the checker
    could not reduce.

**Timing, measured.** Startup alone is 0.19 s. Gate times, current tree:
nat_proofs 0.42, int_proofs 0.47, qext_proofs 0.47, rat_proofs 1.61, qrat_proofs
5.66, probe 1.69, probe.payoff 6.59. The pre-unit tree -- `git show HEAD:` copies of
both qrat files, checked side by side -- measured 5.66 s for qrat_proofs.bend, so
the new fill adds nothing measurable: within noise it is the same number. The
file's ~5.5 s is therefore pre-existing and still above the one-second rule; the
cost is in the older QExt fills, and finding which one dominates is the next
performance item rather than a consequence of this unit.

**Status.** All seven gates print `All terms check.`; `probe.payoff.bend` grew
from thirty-two defs to **thirty-four** -- the law from the caller's side at its own
presentation (sixteen hypotheses, every one of them a fact a caller already holds)
and a literal instance at 1 + sqrt 2 with radicand 2, where norm(1 + sqrt 2) = -1,
the square 3 + 2 sqrt 2 has norm 1, and (-1)*(-1) = 1, with every hypothesis
`{==}` except `hc`, which is the law's own instance. `scratch.bend` prints its
triple unchanged. Law counts, transitive over imports: nat 128, int 32, qext 34,
rat 226, qrat.bend **253** (+1: `QExt.norm.mul`, so the file's own QExt inventory
is 27). What is still open on this side is "no zero divisors when the norm is
non-zero".

## Where qrat_proofs.bend's five and a half seconds live: a bisect, a profile, and a 4 MB normal form (measured)

Round twelve ended with the fill free and the file still at ~5.5 s. This round
finds out where that time is, because the one-second rule is a rule about the
checker and not about one fill.

**The profile.** `node --cpu-prof` over a full check of src/qrat_proofs.bend:
5,639 ms sampled, of which `term_wnf` (weak head normal form) **2,325 ms**,
`term_compare` **2,187 ms**, garbage collector 309 ms, and every remaining
entry under 200 ms -- `term_higher` 199, `parse_term_ops` 35, `term_check` 25,
`term_infer` 18. So essentially the whole file's cost is conversion: normalizing
terms and comparing them. Nothing else is worth optimizing.

**The bisect.** Prefix cuts of the file at def boundaries, checked as
`src/pr_tmp_cut.bend` (a prefix reports its unfilled laws as TODOs, but the term
checks still run -- the run that first showed this printed `Error: 1 TODO found.`
after 5.92 s, i.e. after the work):

| cut at | elapsed | what it adds |
| --- | --- | --- |
| line 56 (imports only) | 1.65 s | the floor |
| line 1084 (all 33 head defs) | 2.05 s | ~0.4 s for the whole head block |
| line 1032 vs 951 (`mul_one`) | +0.35 s | the canonical-spelling fill |
| line 1378 (`conj_mul` complete) | 5.35 s | **+3.33 s: `Q.QExt.conj_mul` alone** |
| line 1548 (`norm.mul` complete) | 5.56 s | +0.2 s |
| end (inv/div fills) | 5.66 s | +0.2 s |

The floor is not this file at all: 1.65 s is what it costs to check the import
graph, and `src/rat_proofs.bend` checked alone is 1.61 s. So of qrat_proofs.bend's
5.66 s, 1.65 s is rat.bend's fills, 3.33 s is one law (`QExt.conj_mul`), 0.35 s is
`QExt.mul_one`, and about 0.35 s is everything else.

**The mechanism.** A deliberately false `{==}` on `QExt.conj_mul`'s conclusion --
x and y at `QExt.of`'s spelled coordinates -- makes the checker print both normal
forms: **4,272,977 bytes of dump**, two sides of one equation. The same file with
a trivial def instead of the false goal takes 0.40 s; with the false goal it takes
1.36 s. One conversion of that pair costs about a second, and the fill has several:
its trans endpoints are written as reduced `QExt{...}` values, so each leg has to
convert a spelled `QExt.mul` application into its normal form.

The normal form is large because `Rat.mul` and `Rat.add` on *constructor*
arguments reduce through `mk`, and each `mk` layer mentions its own gcd,
numerator and denominator several times over. Stack a few of those (`add(mul A B)
(mul p (mul C D))`, which is one QExt.mul coordinate) and the term is megabytes.
At *variables* none of it reduces, and the conversion is a short structural walk.

**What is not the problem.** Citing a spelled law is cheap when the slot's
spelling matches the law's conclusion: `Rat.mul.neg_neg.reduced` cited at two
`Rat{Rat.num(..), 1n+dp}` factors costs **+0.08 s** over the import floor
(1.64 s to 1.72 s). So the fix is not to stop using the reduced laws -- it is to
stop *converting into their normal forms*.

**A measurement lesson.** A `{==}` probe whose two sides are written the same way
short-circuits: three shapes (a spelled `Rat.mul`, a stuck one, a product of two
negated spelled pairs) each cost under 0.03 s that way, which says nothing about
what they cost when they differ. The false-`==` dump is the measurement; identical
sides are not. Related: a probe file at the repo root needs root-relative imports
(`./src/nat.bend`), while a file inside `src/` needs sibling ones (`./nat.bend`) --
copying a `src/` file to the root breaks on `no such file` in 0.25 s.

**The plan this measures out.** Restate the expensive laws the way round twelve
restated `QExt.norm.mul` -- arbitrary QExt values, the spelled coordinates supplied
as hypotheses, so every term in the statement and the fill stays stuck:
`conj_mul` first (3.33 s, and its content is already one citation of a reduced law),
then `mul_one` (0.35 s). That projects qrat_proofs.bend to roughly 2.2 s. Below
one second needs the floor too: `rat_proofs.bend`'s own 1.6 s is the next bisect,
and it is 5,511 lines of fills this file imports.

## conj_mul restated at stuck terms: the same statement, 3.3 seconds cheaper (measured)

Round thirteen found where the time was (one law: `Q.QExt.conj_mul`, 3.33 s, from
conversions into megabyte normal forms) and why (spelled Rat arithmetic normalizes
through `mk`, and each `mk` layer repeats its own gcd and coordinates). This round acts
on it. No law is added, removed or weakened: the same fact is stated over arbitrary
values, and the spelled statement becomes its instance.

**The restatement.** `QExt.conj_mul` now takes arbitrary x and y with the spelling the
identity needs supplied as hypotheses: `hix`/`hiy` name the two *imaginary* coefficients
as the spelled pairs `Rat.of(mq,mn,dq)` and `Rat.of(sp,sn,ds)`, `h1`/`h2` are their
coprimality -- exactly what `Rat.mul.neg_neg.reduced` asks for -- and `gx`/`hx`/`gy`/`hy`
are the four denominators' positivity, the only hypothesis the arbitrary-value Rat laws
in the imaginary lane want. The spelled statement it replaces is its instance:
x := `QExt.of(np,nn,dp,mq,mn,dq)`, y := `QExt.of(rp,rn,dr,sp,sn,ds)`, where the four
positivities and the two namings are all `{==}` and only the coprimality carries over. So
the old statement follows from the new one, and `probe.payoff.bend` is written that way:
`probe.conj_mul` still states the spelled conclusion, and its body now calls the law with
six `{==}` hypotheses and h1/h2.

**The fill.** The same two Rat lanes at arbitrary values. The `match` puts constructors in
place of x and y, so both sides reduce to their coordinates and every `Rat.mul` among them
is *stuck*: that is what makes the term cheap. The real lane transports the product of the
imaginary coefficients into the spelled spelling (two congs along hix/hiy), spends the
reduced law on the bracket `mul(neg xi, neg yi) = mul(xi, yi)`, and replays the transport
backwards so the lane ends on the spelling the goal uses. The imaginary lane is the
neg_add/mul_neg chain as before, with gx/hx/gy/hy in the slots that were `{==}` when the
coefficients were spelled. The only spelled terms left in the fill are the two the reduced
law is stated about -- and citing it there is cheap, which round thirteen measured
separately (+0.08 s).

**One checker detail this cost a run.** `Equal.trans`'s first leg needs the middle
endpoint to be what that leg *concludes*, not the normal form of the left endpoint.
Writing `QExt{add(P,Q), neg(L0)}` -- the left side's own reduction -- as the middle made
the checker demand an evidence of type `{X == X}` (it had unified the two endpoints),
while the `qext.re` witness proves `{X == Y}`: `expected : {X == X}` against
`observed : {X == Y}`. The old spelled fill had the same shape and passed because its left
endpoint was `conj(mul(d, QExt.of(..), QExt.of(..)))`, whose normal form *is* the first
half of the lane rather than the middle. Spelling the middle as the lane's result fixed it.

**Measured after.** `src/qrat_proofs.bend` **2.29 s** (was 5.66), `probe.payoff.bend`
**2.96 s** (was 6.59), and conj_mul's own contribution is now **+0.03 s** by the same
prefix cut that used to read +3.33 s (cut before the def 2.04 s, cut after it 2.07 s).
Every other gate unchanged: nat_proofs 0.57, int_proofs 0.47, qext_proofs 0.48,
rat_proofs 1.58, probe 1.75, and `scratch.bend` prints its triple. Law counts unmoved --
nat 128, int 32, qext 34, rat 226, qrat 253 -- because a restatement changes what a
statement is stated over, not how many there are.

**Where the remaining 2.3 s is.** Now the floor dominates: 1.65 s of qrat_proofs.bend is
its import graph, and `src/rat_proofs.bend` checked alone is 1.58 s. A coarse prefix
bisect of that file (single runs, and the deltas are noisy -- cuts in one region read
1.86 to 2.29 s -- so treat this map as plus or minus 0.3 s): imports only 0.63 s, then
about 0.4 s in the region around line 2288 (`Rat.add.arb.coords`), about 0.9 s between
lines 3075 and 4282, about 0.4 s around line 4908, and not much in the other four
thousand lines. Sub-second for the qrat layer therefore means work on those Rat fills
rather than more QExt restatements. `QExt.mul_one` (0.35 s) is the last qrat law worth
restating, with the caveat its own comment records: at an arbitrary value `x * 1 = x` is
*false* -- the product comes back normalized -- so its stuck form has to carry the
canonical presentation as a hypothesis, exactly as this round did for conj_mul.

## The zero-product law at the Rat level: what "the goal's written form" means, and a grammar corner (measured)

The goal this round was the Rat-level zero-product law -- the forcing lemma the
roadmap names for "no zero divisors when the norm is non-zero". It is landed, as
`Rat.mul_eq_zero`, with `Rat.zero_mul` under it and `Nat.div_self.pos` added to the
Nat inventory on the way. The two measured facts below are the round's real content;
earlier rounds had not hit either.

**The statement: the disjunction moves into the caller's hands.** "x*y = 0 implies
x = 0 or y = 0" has no form here. An equation has two sides, not a disjunction, and a
hypothesis is evidence of a *true* equation -- so "y is non-zero" cannot be handed
over either. The form that is expressible is the unit form:

    x * y = 0   and   y * q = 1   ==>   x = 0

with q a right inverse of y. That is what `Rat.mul_inv.gt`/`.lt` produce, and their
branch evidence *is* what "y is non-zero" means in this development (round four says
so in as many words), so the law carries no sign at all: no GT/LT hypothesis, no
numerator spelling, only the equation, and the branch lives in whoever supplies hq.
The fill is the chain the statement is shaped around --
x = x*1 = x*(y*q) = (x*y)*q = 0*q = 0 -- which is `Rat.mul_one` read backwards, hq
under a congruence, `Rat.mul_assoc.arb` read backwards, hz under a congruence, and
`Rat.zero_mul`: five citations, no rewriting machinery.

**Measured: a fill's type has to be the goal's *written* form, not its normal form.**
The first attempt at `Rat.zero_mul` was a single `Rat.mk.diag` call -- the law that
says a diagonal numerator over a positive denominator is zero, which is what a zero
product's mk produces -- and it was rejected in a way no earlier round had produced:

    expected : {Rat.mk(Int.mul(Int{0n,0n}, xn), Nat.add(xd, 0n)) == Rat{Int{0n,0n},1n} : Rat}
    observed : {Rat{Int{Nat.div.fin(Nat.divmod(0n, ...)), ...}, Nat.div.fin(...)} == ... : Rat}

Both sides denote the same value and each subterm of the first reduces to the matching
subterm of the second, and the check still fails: the comparison is on the *written*
term. `Rat.mul(Rat.zero(), Rat{xn,xd})` unfolds (delta) to
`Rat.mk(Int.mul(Int.zero(), xn), Nat.mul(1n, xd))` with the arguments not further
reduced, and a `{==}` leg does not bridge that to a differently written term -- nor
does a `{==}`-leg between two spellings of the same value. What bridges it is an
explicit `Equal.cong` over the equation between the numerator's two spellings
(`Int.mul_comm` then `Int.mul_zero`) with both endpoints written out. The working fill
is that cong followed by `Rat.mk.diag` at `Nat.mul(1, xd)` with `mul_pos` for the
positivity. The rule to carry forward: a `{==}` leg proves an equation that holds by
computation, but only when the two sides are written the same way -- every earlier
fill in this repo happens to be, which is why this had not come up.

**Measured: a qualified def name takes bare parameters only.** Writing the fill as
`def R.Rat.mul_eq_zero(n: I.Int, d: Nat, fx: {...}, ...)` -- parameters typed, or
marked with `+` -- is a *parse* error ("expected : a name / observed : '+'"), while the
same header parses in a file of its own and while the unqualified helper
`def Rat.add_neg.coords(+xp: Nat, ...)` has used typed parameters all along. Bare
parameters, on the other side, leave every parameter's type at `Quant`, and the
return-type ascription then fails to match ("expected : int.Int / observed : Quant").
The way through is the wrapper the repo already uses for its biggest fills: the chain
lives in a typed helper in the file's own namespace (`Rat.mul_eq_zero.chain`) and the
law's fill is one call to it, `def R.Rat.mul_eq_zero(n, d, fx, ...)`, whose bare
parameters the helper's signature pins. `Rat.add_neg.coords`/`R.Rat.add_neg` is the
same shape one level down.

**What the Nat side needed, and what it did not.** `Nat.div_self` is stated over
`1 + ap`, and `Nat.div` does not reduce at a variable divisor (`divmod` matches on the
divisor), so `div(a, a) = 1` for an `a` that is merely *positive* was a real gap:
`Nat.div_self.pos` is that law, a case split whose `0n` branch is `Empty.absurd` over
`lt_ne_eq` against the positivity witness and whose successor branch is the landed law.
The fill that landed does not need it in the end -- `Rat.mk.diag` is stated over a
positivity witness rather than a successor spelling, and reaches `1 + ap` itself with
`pos_witness`. So it stays as inventory, the missing case of a published family, and
the honest note is that nothing cites it yet.

**Status.** All five `src/*_proofs.bend` check, `probe.bend` (two new caller-side
defs and a literal instance) checks, `probe.payoff.bend` checks, `scratch.bend` prints
its triple. Law counts, transitive over imports: nat 129, int 32, qext 34, rat **229**
(+1 Nat, +2 Rat), qrat **256**. What is still open is the QExt half of the unit: the
zero-divisor statement itself -- `x*y = 0` with a non-zero norm giving `y = 0` -- for
which this law, `QExt.mul_inv` and `QExt.norm.mul` are the machinery.

## The zero-divisor law: the norm becomes a unit witness, and y a spelling (measured)

The unit's second half, and the statement the roadmap has been pointing at since the
norm was proved multiplicative: no zero divisors when the norm is non-zero. It is in
as `QExt.mul_eq_zero`, with `QExt.mul_zero` under it and two new payoff probes. Both
fills checked on the first run; the round's content is the shape of the statement, and
one measurement that says the hypothesis cannot be weakened.

**The two things that travel as hypotheses.** "norm(d,x) is non-zero" never appears in
the law. What appears is a *unit witness*: `zi`, an inverse of x, together with
`hi : x * zi = 1`. That is exactly what `QExt.mul_inv.gt`/`.lt` produce -- one per sign
of the norm's spelling -- and their branch evidence is what "non-zero" means in this
development, so the law carries no sign at all and the norm is not mentioned. The other
hypothesis is the spelling of y: `QExt.of`'s six coordinates plus the two
`Rat.mk.fixed` bridges that `QExt.mul_one` asks for. That one is not stylistic either.
`y * 1 = y` is false at an unreduced coordinate (the product comes back normalized --
round five measured it), so `QExt.mul_one` has a variable form only at the canonical
presentation, and a chain whose first step is `y = y * 1` inherits that restriction.
The fill is then the chain the statement is shaped around,

    y = y*1 = y*(x*zi) = (y*x)*zi = (x*y)*zi = 0*zi = 0

with `QExt.mul_one` backwards, hi under a congruence, `QExt.mul_assoc` backwards,
`QExt.mul_comm` under a congruence, hz under a congruence, and `QExt.mul_zero` to
finish. `QExt.mul_assoc` is the only law in the chain wanting positivity witnesses --
six of them, and four are `{==}` because y is spelled, so the fill's only real choice
is which witness goes in which slot.

**`QExt.mul_zero`, the step the chain ends on**, is componentwise like `QExt.add_zero`:
each coordinate is one or two `Rat.zero_mul` rewrites (a congruence each) plus
`qext.nat.mul_zero` for the one product whose left factor is the radicand coefficient -- a
Rat whose denominator is the base 1, which no `Rat.mul_zero` spelling reaches -- and the
last legs are `{==}`, because `Rat.add(0, 0)` reduces to `Rat.zero()` on its own (both
numerator products carry a zero literal and `Nat.mul(1, 1)` computes to 1). `Rat.zero_mul`
is what made this cheap, and that is what the previous round added it for: with the zero
on the left the numerator of a Rat product collapses by computation but the denominator
does not, and the way through is `Rat.mk.diag`, which takes a positivity witness rather
than a successor spelling.

**The hypothesis is not cosmetic (measured).** At `d = 4` the element `-2 + sqrt 4` has
norm `4 - 4 = 0` and is a genuine zero divisor: `(-2 + x)(2 + x) = x^2 - 4 = 0` at
`x^2 = 4`. `probe.payoff.bend` records both halves at literals -- the product is
`QExt.zero()` and the norm is `Rat.zero()` -- and each closes by `{==}`, so the witness
costs nothing to state. Neither factor is zero, so with `norm(d,x) = 0` the conclusion
`y = 0` is simply false: nothing weaker than "the norm is non-zero" can carry this law,
and the honest statement of what the extension has is a *conditional*: units are not zero
divisors, and every element with non-zero norm is a unit.

**Status, and one honest caveat about the one-second rule.** All five
`src/*_proofs.bend` check, and they are now 0.34-0.44 s each. `probe.bend` (1.70 s) and
`probe.payoff.bend` (3.16 s, four new defs: two caller-side, one literal instance of the
zero-divisor law, and the `d = 4` witness pair) both check. The two consumer files are
*above* one second and this unit did not change that -- 1.76 s and 3.02 s before it -- so
the rule holds for the library and not for the consumer tests. A prefix bisect of
`probe.payoff.bend` (twelve of its thirty-nine defs 2.53 s, twenty 2.67 s, twenty-six
2.58 s, thirty-two 3.10 s) shows the cost is spread across the caller-side defs with no
hotspot: what each one pays is instantiating a law whose fill is stated over spelled
coordinates, which is the same conversion cost round thirteen profiled, and removing it
would mean not calling the published laws at their own presentations -- that is, giving
up exactly the coverage the file exists for. Law counts, transitive over imports: nat
129, int 32, qext 34, rat 229, qrat **258** (+2 QExt: `mul_zero`, `mul_eq_zero`).

## The norm's identities, and the spelled presentation costing 6.7 seconds again (measured)

The last items on the QExt inventory, and a repeat of round fourteen's lesson in a
new place: `QExt.conj_neg`, `QExt.norm.zero`, `QExt.norm.one`, `QExt.norm.conj`,
`QExt.norm.neg` are in, and the `d = 4` boundary moved from the probe file into the
library as `QExt.zero_divisor.d4` and `QExt.zero_divisor.d4.norm`.

**Three of them are free or nearly so.** `QExt.conj_neg` is the *same term* on both
sides once the projections come off -- conj(-x) has real `re(neg x) = -re(x)` and
imaginary `-im(neg x) = -(-im(x))`, and -(conj x) has `-re(conj x) = -re(x)` and
`-im(conj x) = -(-im(x))` -- so the fill is the match and `{==}`. `QExt.norm.zero` and
`QExt.norm.one` are one `qext.nat.mul_zero` step each plus a closing `{==}`: the first
product in each reduces on its own (0*0 and 1*1), the second is `QExt.nat(d)*0` whose
left factor has denominator 1 and so is out of reach of every `Rat.mul_zero` spelling,
and after it `Rat.add(0, -0)` is `Rat.zero()` and `Rat.add(1, -0)` is `Rat.one()` by
computation.

**The two invariances cost 13 seconds at the spelled presentation, and 0.2 after
restating.** `QExt.norm.conj` and `QExt.norm.neg` were first written the way
`QExt.conj_conj` is, over `QExt.of`'s six coordinates with the coprimality hypotheses
that `Rat.mul.neg_neg.reduced` wants. The fills checked, and the file went from 2.3 s
to **15.3 s**: prefix cuts (at true def boundaries -- a cut inside a def aborts the
parse in 0.4 s and reports "expected : a term / observed : end of input", which is
what three of the first cuts were doing before the numbers were believed) put
`norm.conj` at **+6.4 s** and `norm.neg` at **+6.7 s**, while `norm.zero`, `norm.one`
and both boundary instances cost about +0.1 s each. This is exactly round thirteen's
mechanism: at spelled coordinates each conversion normalizes through mk chains, and
the cost is in the *conversion*, not in the proof. Restating both laws at arbitrary
`x`, with the spelling the identity needs supplied as a hypothesis (`him` names the
imaginary coordinate as `Rat.of(mq,mn,dq)`; `norm.neg` also takes `hre`) drops the
file to **2.58 s** -- the fills become three-step transports at stuck terms, spelling
out to the named pair, applying the reduced law, and spelling back -- and the spelled
statement survives as the *instance*, which is what the new
`probe.norm.neg.instance` writes: at `x := QExt.of's` coordinates both naming
hypotheses are `{==}`. Round fourteen did this to `QExt.conj_mul`; this round is the
same fix applied to two more laws, and the numbers are the same order.

**The boundary is stated at literals, and that is measured rather than lazy.** The
parametric form over a radicand `c*c` -- `(-c + x)(c + x) = x^2 - c^2 = 0` -- stops one
step short of the canonical form: the two real coordinates multiply to the difference
pair `Int{0, c*c}`, whose magnitude is `Nat.mul(c,c)`, and `mk`'s divisor is then
`gcd(mul(c,c), 1)`. `Nat.gcd` splits on its first argument (`a = 0` or `a = 1 + ap`), so
it cannot start on a product, and the reduction stalls before the numerator can be seen
to be zero. A general statement would need the scaling half of the normalization again
-- the `Rat.mk.scale` family and its Nat witnesses -- which is a unit of its own; the
instance is what records the boundary, and its comment says so. Both halves close by
`{==}`, so the record costs nothing.

**Status.** All five `src/*_proofs.bend` check at 0.33-0.44 s; `probe.bend` 1.65 s and
`probe.payoff.bend` 3.71 s check (the latter up 0.55 s for eleven new defs: six
caller-side, one literal instance, two boundary citations and their two norm/probe
twins); `scratch.bend` prints its triple. Law counts, transitive over imports: nat 129,
int 32, qext 34, rat 229, qrat **265** (+7 QExt: the five identities and the two
boundary instances).

## The checker update: the literal wall was upstream all along (measured)

Round seventeen ended with a measurement that reframed the next unit: a nat literal in
proof land is a `Succ` tower, and beyond about 10^3 nodes the checker did not get slow,
it **died** -- "the machine stack overflowed", reported in 0.26 s, at depths 10^4 and
above. The question that followed was whether to build a binary representation for
proof land. This round checked the checker's own history first, and the answer was that
the work had already been done upstream.

**The update.** The `bend` checkout at `0b7e2b11` (2026-09-18, a 2.0.5-era tree) was
fast-forwarded to `d3790917` (2026-09-23, **Bend 2.0.27**) -- 214 commits, ours an
ancestor of theirs, nothing of ours ahead, so a clean `--ff-only` with no merge. The
canonical repo is `bendlang/bend` (the one this project's README links); the checkout's
own `origin` is `phenomenon0/bend`, which was already in sync at the old commit. The old
SHA is recorded here because reverting is a `git checkout 0b7e2b11`.

**Why that was the fix.** CHANGELOG 2.0.24 (2026-09-21): *"A string or nat literal is
one `Lit` node in the checker (PRs #907 and #924): a literal unfolds one constructor at
a time when it is compared, matched or checked, so 50 defs of 1000-char strings check in
0.14 s and 74 MB instead of 4 s and 2.6 GB, **a 200k-char literal checks instead of
overflowing the stack**, ... and `1n+0n` is `1n`."* Exactly the failure we measured,
fixed two days after our checkout's commit.

**Measured after the update** (same probe, `Nat.sub(K, 0n) == K` for K = 10^k):

| K | before (node, old checker) | after (2.0.27) |
|---|---|---|
| 10^3 | 0.34 s, ok | 0.36 s, ok |
| 10^4 | 0.26 s, **stack overflow** | 0.18 s, ok |
| 10^5 | 0.28 s, **stack overflow** | 0.17 s, ok |
| 10^6 | 0.87 s, **stack overflow** | 0.19 s, ok |
| 10^7 | -- | 0.17 s, ok |

**The gates, re-run on 2.0.27.** Every one passes and every count is identical: five
`src/*_proofs.bend` (`nat_proofs` "All terms check.", int 32, qext 34, rat 229, qrat
265), `probe.bend` 1.85 s, `probe.payoff.bend` 4.34 s, `scratch.bend` printing its
triple. The library checks got faster, 0.33-0.44 s down to 0.18-0.36 s.

**The invocation changed, and it needs Bun.** `bend2/main.ts` now guards its CLI with
`if (import.meta.main) { if (typeof Bun === "undefined") { say("bend runs on Bun...");
exit(1) } }`, so `node bend2/main.ts <file>` prints the install line and exits; the
`else` branch registers a Node module hook, so *importing* the module still works from
Node. Bun 1.3.11 is already in this box's nix store, which is what these runs used.
`nix shell nixpkgs#bun -c bun ...` is the durable form, but it could not be verified
inside this session's file sandbox -- nix's fetcher cache lives outside the workspace
and the write is denied -- so it is documented as the form to use, not as a measured
one. `bend.ts` is human-written and marked do-not-edit in its own `AGENTS.md`.

**Two ceilings remain, both now measured.** Arithmetic on literal operands still
recurses over the tower -- `Nat.mul`, `Nat.div` and `Nat.gcd` at 10^3 and 10^4 operands
stack-overflow -- and a nat literal is capped at `4294967295n` (`bend.ts:2352`, 32-bit),
so at 10^5 the probe fails with *"expected : a nat literal up to 4294967295n"* rather
than computing. The `Lit` node fixed storage, comparison and matching; it did not make
the *operations* native.

**What that does to the plan.** The "build the binary representation first" question is
answered in halves. The storage half was already fixed upstream, so writing concrete
numbers -- even ten-million-sized ones -- is fine now, and `TOWER-PLAN.md` §4.2 and
README item 3 were rewritten to say so. The arithmetic half is a *reducer* change of the
same kind as the `Lit` node: when both operands of a `Nat` operation are literals,
compute natively as the compiled lanes already do (`comp.ts:161` maps `Nat` to W64 with
native `nat_add`/`nat_mul`/`nat_divmod`) and box the result as a literal. That is a
proposal for the checker's owner, not a patch this repo carries. The bignum half --
coordinates past 2^32 -- is a later question whose shape should be decided by measured
coordinate sizes from real sketches, with `Word(n)`'s bit vectors in `base.bend` as the
obvious substrate.

## The literal-arithmetic fast path: four operations, a wrapper, and the cost of touching a hot loop (measured)

Round seventeen's proposal -- compute `Nat` operations natively when their operands are
literals -- became a branch, and the branch is parked rather than proposed: it works, but
the interesting result is where the *cost* came from and what it says about editing
`bend.ts`.

**What the wall is.** Not literal storage (2.0.24's one `Lit` node is fine) and not step
count: `Nat.add`, `Nat.mul`, `Nat.div` and `Nat.mod` are not tail-recursive, so a literal
operand costs its value in nested `Succ` on the way out, and `divmod`'s loop runs the
dividend. Measured on the parent commit, before any patch: `mul` dies between 100^2 and
300^2, `add` between 10^4 and 3*10^4, while `sub` and `cmp` are fine at 10^8 -- *both are
tail-recursive, so both were dropped from the fix*, which is why the table has four
operations and not six. `div(10^8, 10^4)` does not finish in 180 s unpatched.

**Three placements, timed interleaved** against the parent on `probe.payoff.bend`, this
repo's arithmetic-heavy gate. Inside `term_wnf`'s `App` case: **+5.5%**. Same plus a
magnitude gate: **+9.4%**. At the `Ref` case, where the operator's name is already in
hand: **+5.5%, then +11%** in a later run -- and a control whose gate could never fire,
which broke coverage and so proved the fast path was doing nothing, *still cost +5%*. The
lines themselves are the cost: a few statements inside that loop, whatever they do.
Moving the call out of the loop into a wrapper at `term_wnf`'s entry -- the loop then
differs from upstream by zero lines -- measured -1.3% and +2.5% on two interleaved runs,
minima 4.31 s vs 4.31 s and 4.25 s vs 4.38 s, i.e. inside run-to-run noise.

**Two folds, both tried and both rejected on measurement**, which is why the fast path
exists at all. Folding `Succ(Lit(k))` to `Lit(k+1)` inside `term_higher` breaks
elaborating `base.bend` itself -- `expected : Word(32n) / observed : Word.Con` at
`IO.fork`'s `Chan.new(A, 1)`, because `lit_step` peels *any* numeric literal as
`Zero`/`Succ` with no type in scope. Folding at the reducer's `App` frame (through
`term_apply`) is sound where it fires and moves no wall: the cost is paid in nested
forcing of lazy cells, not at any site a fold can reach.

**State.** Branch `nat-prim-literals` on the `phylliida` fork at `54aa1206`: 44 lines in
`bend2/bend.ts` plus a 30-line `tests/base/nat_lit_arith.bend` that the parent commit
fails with *"the machine stack overflowed"* and the branch prints `2` for. Verified on
the branch: every gate here, plus coverage of `add(10^6,1)`, `mul(10^4,10^4)`,
`div(10^8,10^4)`, `mod(10^6,7)` and a nested `add(mul(8100,12345),5499)`. Parked by
choice -- no PR, no issue -- so it stays a measurement, not a claim.

## Step 0.1 of the tower plan: the checker shares, so a chain is a list of named definitions (measured)

The plan's first probe asked whether the checker shares terms, because a geometric step
uses the previous point three or four times and a naive encoding of a 30-deep chain is
3^30 nodes. Three encodings, each at a range of depths, one probe file per run, 0.17-0.18 s
being the floor these runs sit on (checker startup):

- **Written out as one expression** (nested `Nat.add`, small values): flat to depth 100,
  under 2 KB of source.
- **One `def` per level, each naming the previous twice**: flat from depth 5 to 30, 1 KB
  of source at 30.
- **The same, with the goal forcing the value** (`{P.fst(A30()) == 1n}`, which has to peel
  thirty levels before it can compare): *also* flat, 0.18 s.

The third row decides it. If the checker materialized the value it would be building a
2^30-node tree; if it substituted named definitions into the caller's term, the goal
itself would explode. Neither happens: reduction is lazy and the value stays shared. The
plan proceeds as written, and Step 5's certificate is a list of named steps -- the same
arrangement the Verus lane reached from the other direction.

The law-application encoding could not be built as §6.1 sketches it, and the reason is
worth keeping: *"expected : a filled definition (an unfilled law is a dead claim: live code
cannot use it)"*. A `law` in `src/*.bend` is a statement awaiting its fill in
`src/*_proofs.bend`, and nothing may call it until that fill exists -- so a chain of law
applications belongs in the `*_proofs.bend` file, which is where Step 5's work happens
anyway. Recorded in `TOWER-PLAN.md` §6.1 with the numbers.

Two syntax facts the probe paid for, now in the plan: a type is `type P is Data:` with its
constructor on the following line (not `type P: P{...}`), and a projector is a plain `def`
with a destructuring body (`P{+f, +s} = p`, then `f`), not a derived field access.

## Step 0.2 measured: fills induct structurally, and a value index carries a tower (measured)

Both remaining Step 0 questions came back yes on the first shape that parsed, and the
second one retires the plan's biggest named risk.

**Induction in a fill.** A laws module declared a recursive user type `TL` with
`TL.append` and `TL.sum` over it, and the law `TL.sum(TL.append(a, b)) ==
Nat.add(TL.sum(a), TL.sum(b))` at variables -- a statement no amount of unfolding
settles. The fill, in a second module, `match`es on `a`, closes the `Nil` branch
definitionally (because `Nat.add(0n, x)` reduces to `x`), and in the `Con` branch calls
*itself* on the tail: the checker accepted a fill that recurses structurally, with the
induction hypothesis arriving at the smaller tower already stated. Two rewrites assemble
it -- the hypothesis, flipped through `Equal.sym` because the goal's occurrence is its
left endpoint, and one associativity step. The recipe is in TOWER-PLAN §6.2.

The durable fact from that exercise is the rewrite orientation, now measured rather than
remembered: **`%e` replaces the goal's occurrence of `e`'s right endpoint with its
left.** `N.add_assoc` -- `(a+b)+c = a+(b+c)` -- could not rewrite `(h + sum t) + sum b`;
its flipped twin `N.add_assoc_rev` closed the proof in one step. That is exactly why
`nat.bend`'s `add_succ` is documented as "stated flipped so rewrites fire left-to-right",
and it means a new law should be stated in the direction its rewrites will need. Four
ascription/orientation combinations were tried and exactly one checked, which is the
cheapest way to have learned it.

**A tower-valued type index.** The `Word` idiom (`type Word.Con<-p: Nat>` plus `def
Word(n: Nat) -> Data`) generalized from a `Nat` index to a tower-valued one: indexed
constructor types `Elem.Base<-v: Nat>` and `Elem.Ext<-t: Tower>`, a type-level `def
Elem(t: Tower) -> Data:` matching on the tower, and

```
def Elem.zero(+t: Tower, x: Elem(t)) -> Elem(t):
  match t:
    case TBase{v}: x
    case TExt{re, im, d}: x
```

which checks -- the checker reduces `Elem(t)` per branch, so `x` has the right type in
both -- and a law may quantify `for +t: Tower for +x: Elem(t)`, a dependent parameter over
a family whose index is a runtime value. So an element type can carry its tower *in the
type*: DESIGN §9.1's route (η) written natively, and the statement that the "relative-ring
crux" may not exist on this side at all. Step 2's operations can be typed `Elem(t) ->
Elem(t)` instead of carrying a tower argument through every law. §3.2 is rewritten to say
so, with the depth-index-plus-`wf` fallback kept for the case where the laws want it.

**Namespace facts, both cost by the probes.** Constructor names are global -- `Nil` and
`Con` are taken by `base.bend`, hence `TNil`/`TCon`, while `Base` and `Ext`, the names
Step 1's sketch uses, are free. A cross-module *pattern* names the constructor under the
module alias with no type in the path (`case L.TNil{}:`); construction across modules was
not exercised. Both probe files are deleted; the recipes are in the plan.

## Step 1 landed: the tower's structural machinery, and what wf's risk turned out to be (measured)

TOWER-PLAN's Step 1 is in: `src/tower.bend` and `src/tower_proofs.bend`, with the new gate
green. Transitive counts: **tower.bend 233** = rat.bend's 229 plus its own four; all six
`*_proofs.bend` gates check (0.34-3.35 s in one run against upstream), and so do
`probe.bend` (1.95 s), `probe.payoff.bend` (4.32 s) and `scratch.bend`'s triple. The tower
gate itself is 1.60 s.

**What landed.** The element type is the tower: `Base{value}` a rational,
`Ext{re, im, d}` = re + im*sqrt(d) with all three parts at the level below, so an
element's shape *is* its level. `Tower.depth` reads it, `Tower.zero` builds the additive
identity at a level (recursively, keeping its radicand slot), and `Tower.lift(t, d)` is
`Ext{t, Tower.zero(t), d}` -- one constructor, so lifting is *constant*-time rather than
merely linear. Four laws: `zero.base`, `depth.lift` and `lift.zero` definitional,
`depth.zero` a structural induction in the fill.

`depth.zero` is the Step 0.2 recipe doing real work on its first outing, and it worked
first try: the match refines the law at the branch, the `Ext` branch calls the fill itself
on the tail, and the orientation rule measured last round (`%e` replaces the goal's
occurrence of `e`'s **right** endpoint with its left) dictated the flipped induction
hypothesis through `Equal.sym`. The three definitional laws are not fillers: `lift.zero` is
the plan's "lift distributes over the level operations" met for `zero`, which is a level
operation and the identity of the level's addition. The `add` and `mul` cases need Step 2.

**`wf`'s risk, answered as sequencing rather than shape.** The plan called `wf`'s shape the
one real design decision in Step 1. Measured answer: its arithmetic half -- "a radicand
positive, levels reduced" -- cannot be stated yet, because positivity needs the ordering
that Step 2 brings; and its structural half is *automatic*, because `Ext{re, im, d}`
requires three towers whose shape is their level, so no value can violate it. What is left
is what the plan actually needs it for: a family `Tower.wf(t) -> Data` with a trivial leaf
and an `Ext` case carrying the three sub-evidences, plus two *transport* defs --
`Tower.wf.zero` and `Tower.wf.lift` -- which are structural inductions in an *indexed*
type, the second consuming the first to build the evidence a lift needs. Those are the
shapes Step 2's positivity evidence will take.

**Three exactness facts, all load-bearing from here.** Evidence at an indexed type does not
survive as an equation: `Tower.wf(Tower.zero(t))` and `Tower.wf(t)` have different indices
(`Tower.Wf.Ext<zero re, zero im, d>` against `Tower.Wf.Ext<re, im, d>`) and no equation
between them is true, which is why `wf.zero` had to become a transporting def. A type
family must be declared *above* the def it references -- base's `Word.Con` sits above
`Word` for the same reason; with the family below, the reference inside the def resolved
too early and importing the file failed with a doubled module path (`tower.tower.... .Ext`,
even though the file checked alone). And laws and defs share *one* namespace, so a law and
a def cannot both be `Tower.wf.lift` -- the def's return type states it instead. A def
parameter used twice also needs `+`, exactly like a law's.

**State.** The checker checkout was returned to upstream Bend 2.0.27 (`d3790917`) for this
round's measurements, so the numbers above carry no patch: the parked `nat-prim-literals`
branch stays on its ref for whenever it is wanted.
## Step 2's operations: the level arithmetic lands, and the checker turns out to check termination (measured)

Step 2's arithmetic is in `src/tower.bend` with its fills, and the tower gate is green at
**240 = rat.bend's 229 plus the tower's own eleven**. `Tower.add(+d, x, y)`,
`Tower.neg(x)`, `Tower.mul(+f, +d, x, y)` and `Tower.one(t)`, with seven laws at spelled
constructor forms -- `add.base`, `add.ext`, `neg.ext`, `mul.base`, `mul.ext` (the
`sqrt(d) * sqrt(d) = d` unfolding the plan's done-when asks for), `one.base`, `one.ext` --
every fill definitional. The five *ring* laws are not proved yet; they are inductions over
the tower and they are the rest of the step.

**The radicand stays an operation parameter**, as planned, and that is what keeps the ring
laws statable: `add(d, x, y)` and `add(d, y, x)` name one radicand, so no law carries a
shape-agreement hypothesis. Operands at different levels are not a value of the theory, so
the mismatched arms return the level's zero and no law reaches them.

**The discovery: bend checks termination.** Writing `mul` the obvious way was rejected --
*"expected : a decreasing self-call (arguments are read left to right: each passed
unchanged until one shrinks)"* -- because the `sqrt(d)*sqrt(d) = d` term needs the im*im
product multiplied by `d`, and that nests one self-call inside another's argument. Four
shapes were measured against it:

| shape | verdict |
|---|---|
| `mul(d, rx, ry)` -- two operands shrinking together | fine: `add` passes with exactly this |
| a let-bound intermediate (`xy = mul(d, ix, iy)`, then `mul(d, xy, d)`) | rejected: a binding is not a subterm |
| operand order / radicand read from the operand instead | same rejection |
| descending on a `Nat` fuel (`case 1n+g:`, recursing with `g`) | **accepted** |

So `Tower.mul` is fuel-driven, which is the shape `base.bend`'s own `Nat.gcd` takes, and
every `mul` law is spelled at a successor fuel (`Tower.mul(1n+g, d, ...)`). Callers pass a
fuel of at least the operands' depth; proving that enough fuel never runs out is part of
the rest of Step 2. The same check constrains the *ring* laws from below: any induction
whose step nests a self-call will need the same treatment.

**Three exactness facts the spellings cost.** Pattern binders are *linear* -- a constructor
field used twice needs `+` in the pattern (`case Ext{+rx, +ix, +dx}:`), or the checker says
*"expected : iy"*, which reads like a missing variable and is not. A law's statement may
only name its `for` parameters: `Ext{rx, ix, dx}` with no `for dx` gives *"expected : a
defined name / observed : dx"*, so no pattern binder is implicitly quantified. And a
fill's parameter list mirrors its law's `for` list exactly, in order -- the checker prints
the expected tail (`@iy -> @dy -> ...`), which settles the order fastest.

**State.** Six gates green, the tower one at 240. Not yet done in Step 2: the five ring
laws, the fuel-sufficiency law, and the route B probe (`Elem(t)`-indexed operations), which
the next round runs to decide whether the indexed route is worth adopting wholesale.

## Route B probed: indexed ring laws state cleanly, and the congruence step is where the index bites (measured)

The bounded probe the plan asked for, run against `Elem(t)` -- the tower as a *type index*
rather than as data.

**What works.** Indexed constructor types (`Elem.Base<-v: Rat>`, `Elem.Ext<-t: Tower>`), a
type-level `def Elem(t: Tower) -> Data` matching on the tower, and
`def Elem.add(+t: Tower, x: Elem(t), y: Elem(t)) -> Elem(t)` all check, with each branch
destructuring its operands because the checker reduces `Elem(t)` once `t` is a constructor.
The ring law states at a variable context with **no shape hypothesis**:

```
law Elem.add.comm:
  for +t: Tower
  for +x: Elem(t)
  for +y: Elem(t)
  {Elem.add(t, x, y) == Elem.add(t, y, x) : Elem(t)}
```

and the probe file reports 231 TODOs = rat.bend's 229 plus those two laws, the predicted
count. That is route B's real advantage: a mismatched-radicand call cannot be written, so
nothing needs hypothesising away -- the crux §3.2 says may not exist, demonstrated rather
than argued.

**Where it bites.** The `Base` branch of the fill closes in one step (`Equal.sym` around
`R.Rat.add_comm`, goal type spelled `Elem(Base{v})`). The `Ext` branch does not: rewriting
inside the constructor needs `Equal.cong`, and its lambda cannot infer an indexed
constructor's index at a variable context. Three spellings measured, one message:

*expected : Elem(d) / observed : Elem.Ext<d>*

-- the checker wants the lambda's *domain* where the codomain belongs, and the ascription's
type makes no difference whether it is written reduced (`Elem.Ext<d>`) or unreduced
(`Elem(LB.Ext{re, im, d})`). The untested candidate is the house helper pattern: a typed def
`Elem.Ext.at(+d, u, xi) -> Elem.Ext<d>` so the lambda returns a declared type rather than an
inferred constructor index. That would need one helper per congruence per constructor, which
is the cost to weigh -- and it is a checker inference limitation, not a mathematical one.

Timings are not a useful signal here: the probe file checks in ~1.6 s, dominated by the
`rat_proofs.bend` import that completes its closure. The cost is in the number of steps and
the wall, not the clock.

**Verdict: Step 2 continues on route A.** Route B buys away the shape-agreement hypotheses
and pays in index-spelled congruence helpers at every induction step. Route A pays once per
operation (the `+d` parameter, and fuel for `mul`) rather than once per proof step. Route B
stays available and measured; if route A's ring laws turn out to be dominated by shape
hypotheses, this probe is where to restart -- with the helper-pattern fix tried first.

Both probe files are deleted, with the recipes in TOWER-PLAN §7 Step 2.

## Route B solved: the wall was the indexed %-ascription, not the index inference (measured)

The probe that round twenty-three left open, finished. Route B -- the tower as a type index
-- is **viable**, and the earlier verdict on it was wrong for a specific and now-measured
reason.

**The helper pattern works.** A typed def

```
def Elem.Ext.at(+d: Tower, u: Elem(d), w: Elem(d)) -> Elem.Ext<d>:
  EExt{u, w}
```

makes the congruence check *as a direct term*:

```
def T3.cong.at(+d, +a, +b, +w, e: {a == b : Elem(d)})
    -> {Elem.Ext.at(d, a, w) == Elem.Ext.at(d, b, w) : Elem.Ext<d>}:
  Equal.cong(LB.Elem(d), LB.Elem.Ext<d>, u => LB.Elem.Ext.at(d, u, w), a, b, e)
```

That checks, and it pins `Equal.cong`'s signature as `(domain, codomain, f, a, b, e)`: the
swapped order, both-slots-the-same, and the no-type-argument forms each fail, the last with
*expected : Type / observed : non-inferrable term*, so the type arguments are required.

**What actually fails is the `%` step.** `%Equal.cong(...)` with an indexed ascription type
was rejected in five spellings -- `Elem.Ext<d>`, `Elem(d)`, the unreduced
`Elem(Ext{re, im, d})`, swapped slots, and both-slots-equal -- all reporting the same pair:

*expected : Elem(d) / observed : Elem.Ext<d>*

and the step *does* fire underneath: the context print shows the first coordinate already
rewritten to `add(d, yr, xr)` when the complaint arrives. Dropping the ascription is not an
option either: the checker answers *expected : ':' / observed : '%'*, so a `%` step must
carry one. The distinguishing feature against the *working* `Base` branch is the hole's slot
type: there the ascription is `Elem(Base{v})` and the hole sits in a `Rat` slot, a plain
type, whereas the `Ext` branch's hole sits in a slot of indexed type `Elem(d)`.

**Direct terms avoid the wall entirely.** Three congruence defs -- `Elem.at.cong` (rewrites
the first coordinate), `Elem.at.cong.r` (rewrites the second), and `Elem.pair.cong`
(composing the two with `Equal.trans`) -- let the law's fill's `Ext` branch be one term
application:

```
case LB.Ext{re, im, +d}:
  LB.EExt{+xr, +xi} = x
  LB.EExt{+yr, +yi} = y
  LB.Elem.pair.cong(d,
      LB.Elem.add(d, xr, yr), LB.Elem.add(d, yr, xr),
      LB.Elem.add(d, xi, yi), LB.Elem.add(d, yi, xi),
      LB.Elem.add.comm(d, xr, yr), LB.Elem.add.comm(d, xi, yi))
```

and the file reports **All terms check.** The law is therefore proved at a *variable*
context, with no shape hypothesis anywhere: `Elem.add.comm: for +t: Tower, for +x: Elem(t),
for +y: Elem(t) {Elem.add(t, x, y) == Elem.add(t, y, x) : Elem(t)}`.

**Why this matters beyond the probe.** The whole point of route B is that a call with
mismatched radicands has no type. Route A's version returns `zero(d)` instead -- a value
`depth` cannot distinguish from a correct element of the same level (measured: the arms
return the caller's own radicand's zero). So A's safety is a convention, B's is a type. The
cost of B measured here is three defs, ~12 lines, per operation; the recipe is in TOWER-PLAN
section 7. Timings are not a signal (the probe checks in 1.7 s, importing rat_proofs).

**Still unmeasured for B**: `mul` under an indexed signature (whether the
`sqrt(d) * sqrt(d) = d` term needs the same Nat fuel the data-tower version needed), the
other four ring laws, and target-file timings.

## Round twenty-five -- Route B's operations: the radicand cannot become an element, and the carrying field is caught by the checker

Route B's `add` was proved in round twenty-four. `mul` is the hard one, because the
`sqrt(d)*sqrt(d) = d` term puts the radicand *into* the multiplication term. Four
measurements, all on `probe.tower.rb.bend` (route B's machinery, law-free, so probes
can import it) and its satellites.

**P1 -- the radicand is not an element.** A def whose body needs exactly what `mul`
needs (multiply a coefficient by the radicand):

    def LB.Elem.crux(+d: LB.Tower, u: LB.Elem(d)) -> LB.Elem(d):
      LB.Elem.add(d, u, d)

    Error:
    - expected : probe.tower.rb.Elem(d)
    - observed : probe.tower.rb.Tower
    Location: LB.Elem.crux

**P2 -- the embedding is blocked, at the relative-ring crux.** `Elem.of(+t: Tower) ->
Elem(t)`, Ext case `EExt{Elem.of(re), Elem.of(im)}`:

    Error:
    - expected : probe.tower.rb.Elem(d)
    - observed : probe.tower.rb.Elem(re)
    Location: LB.Elem.of

(The first run of this probe reported `expected : a declared constructor` because I
typed `EElem` for `EExt` -- my typo, not a measurement. Worth recording as a reminder:
when an error names a constructor, check the spelling before believing it.)

**P3 -- a type index is legal.** `type ElemT.Ext<-K: Data> is Data`, `TExt{re: K, im: K}`,
and `def ElemT(t: LB.Tower) -> Data` whose Ext case returns `ElemT.Ext<ElemT(d)>`: 229
TODOs, i.e. rat.bend's law count and nothing of mine. The element family may therefore
be indexed by the coefficient *ring*.

**P4 -- the carrying shape checks, and it does not need fuel.** With
`ElemC.Ext<-K: Data>` of `CExt{re: K, im: K, dr: K}` (`dr` = the radicand as an element
of the coefficient ring) and the family returning `ElemC.Ext<ElemC(d)>`, a mul whose Ext
case is

    CExt{ElemC.add(d, ElemC.mul(g, d, xr, yr),
            ElemC.mul(g, d, ElemC.mul(g, d, xi, yi), xdr)),
         ElemC.add(d, ElemC.mul(g, d, xr, yi), ElemC.mul(g, d, xi, yr)),
         xdr}

reports 229 -- it checks. And so does the same term with the fuel removed and the
recursion written `ElemC.mul(d, ...)`: 229 again. Route B's `mul` needs no fuel, because
it descends on the level index `d`, a subterm of the `Ext{re, im, d}` pattern, while
route A descended on a plain tower parameter where nothing shrank. The fuel-sufficiency
law leaves the plan.

**P5 -- the carrying field is not verified, and the checker says so.** `law
ElemC.add.comm` for all `x, y : ElemC(t)`, with the congruence helpers for the
three-field constructor (`ElemC.ext.at`, `.at.cong`, `.at.cong.r`, `.pair.cong`,
mirroring round twenty-four's recipe with the third field held fixed), fails at the Ext
branch with

    expected : {CExt{..., xdr} == CExt{..., ydr} : ElemC.Ext<ElemC(d)>}
    observed : {CExt{..., xdr} == CExt{..., xdr} : ElemC.Ext<ElemC(d)>}

The goal's third field is the *right* operand's carried radicand; the term I can build
carries the left one's. So `add.comm` is false for elements whose carried radicands
disagree. This is what route A could not give: route A's mismatch arms return
`zero(d)`, which `depth` cannot distinguish from a correct element, so mismatches are
silent and every law holds vacuously. Under route B a mismatched call is unprovable.
It is not untypeable, which is what safety-by-construction would require.

Also measured here, a cross-file rule: a probe that cites a library *law* must import
the proofs file as well. `probe.tower.law.bend` failed with `expected : a filled
definition (an unfilled law is a dead claim: live code cannot use it) / observed :
src/rat.Rat.add_comm` until `import ./src/rat_proofs.bend` was added -- the same
"unfilled law is a dead claim" rule as within a file, one level up.

The clean statement of a law wants the radicand as an *index* (so operands share it by
construction); the operations want it as *data* (`mul` must multiply by it). The level
family cannot supply the index: it dispatches on `t`, and no radicand element is
determined by `t`. An operations record passed per level is the untested reconciliation.

## Round twenty-six -- No dictionaries in bend: the operations record is not expressible, and the design question closes

Round twenty-five ended with one untested reconciliation: index the element by the
radicand and pass the operations in per level. Four probes, all tiny, and the answer is
no -- for two independent reasons.

**P1 -- a `Data` type cannot hold a function field.**

    type Ops<-K: Data> is Data:
      OpsRec{add: K -> K -> K, mul: K -> K -> K}

    Error:
    - expected : Data
    - observed : Type
    Context:
    - K : Data
    Location: OpsRec

Function types have kind `Type`; a `Data` declaration's fields must have kind `Data`.

**P2 -- the parenthesised arrow spelling is a Sigma, not a function type.**

    type Ops2<-K: Data> is Data:
      OpsRec2{add: (K, K) -> K, mul: (K, K) -> K}

    Error:
    - expected : Type
    - observed : Sigma
    Location: OpsRec2

So function types are written with bare arrows (`K -> K -> K`), and that is the kind
information worth keeping: they are `Type`-kinded, which is exactly why P1 fails.

**P3 -- a def cannot take a type parameter.** With the radicand as an index and a
dependent parameter type (both fine on their own):

    def EB.k(+K: Type, +dr: K, x: EB.Ext<K, dr>, y: EB.Ext<K, dr>) -> EB.Ext<K, dr>:
      x

    Error:
    - expected : Data
    - observed : Type
    Location: EB.k

**P4 -- and `Data` instead of `Type` does not help.** The same def with `+K: Data`: the
same error, `expected : Data / observed : Type`, at the def. Nor is it about the
function type specifically:

    def Ops.add(+K: Type, f: K -> K -> K, x: K, y: K) -> K:
      f(x, y)

    Error:
    - expected : Data
    - observed : Type
    Location: Ops.add

Def parameters must be data values. Bend therefore has no type parameters and no
function parameters: no dictionaries, no type classes, no operations records. This is
not a limitation of the family syntax -- dependent parameter types are fine, and P1 of
round twenty-five (`u: LB.Elem(d)`) checked as a signature, failing only in the body.

**What it settles.** Operations must be dispatched on a *value*, which is what route B's
level family does (`def ElemC(t: LB.Tower) -> Data`). The radicand can thus be a type
index or a value but never both, and the carrying design of round twenty-five is the only
expressible shape rather than one option among several. Its accepted cost stands:
elements whose carried radicands disagree are unprovable, not untypeable.

The residual hole is narrower than that sounds. Elements at different *levels* are
already untypeable under route B, since the Ext case is indexed by the radicand tower --
`Elem.Ext<d>` -- so two elements at `Ext<d1>` and `Ext<d2>` cannot be passed to the same
operation. What remains open is two different elements representing the *same* radicand
at the same index. Pinning the carried field to the index is exactly the embedding, which
fails in the Ext case with `expected : Elem(d) / observed : Elem(re)` (round twenty-five
P2), and indexing the element by the radicand *element* would need a def generic in that
element's type, which P3/P4 rule out. The hole is structural in bend as it stands. Two
ways out, both unmeasured: an upstream bend feature (type or function parameters), or a
working embedding -- which for a *base* radicand is trivial (`Base{v} -> EBase{v}`) and
fails only when the radicand is itself a tower, i.e. exactly the nested-radicand case a
deep chain produces.

### Addendum -- the safety claim itself, with a control

The mismatch test in P1 could not run inside the polymorphic def, so it was redone at
concrete indices, where no type parameter is needed. A dependent index is legal
(`type EC.Ext<-K: Data, -dr: K>`) and the rejection is exactly the one wanted:

    def EC.op(x: EC.Ext<EC.Base<0n>, ECBase{0n}>,
              y: EC.Ext<EC.Base<0n>, ECBase{0n}>)
       -> EC.Ext<EC.Base<0n>, ECBase{0n}>:
      x

    def EC.op.bad(x: EC.Ext<EC.Base<0n>, ECBase{0n}>,
                  y: EC.Ext<EC.Base<0n>, ECBase{1n}>)
       -> EC.Ext<EC.Base<0n>, ECBase{0n}>:
      EC.op(x, y)

    Error:
    - expected : EC.Ext<EC.Base<0n>, ECBase{0n}>
    - observed : EC.Ext<EC.Base<0n>, ECBase{1n}>
    Context:
    - x : EC.Ext<EC.Base<0n>, ECBase{0n}>
    - y : EC.Ext<EC.Base<0n>, ECBase{1n}>
    Location: EC.op.bad

Control: the same file with agreeing radicands prints `All terms check.`, so the
rejection is the radicand index and nothing else.

This is a real safety property -- two elements claiming different radicands are
untypeable -- but it is available only per concrete ring, because a def generic in the
coefficient type is impossible (P3/P4). A tower of unbounded depth therefore cannot be
covered this way, which is the point in favour of the level family and the carrying
design despite their unprovable-not-untypeable mismatch cost.

## Round twenty-seven -- The embedding and typed arithmetic are mutually exclusive

Round twenty-five's P2 left the embedding failing with `expected : Elem(d) / observed :
Elem(re)`. Three probes show that the failure depends entirely on which index keys the
Ext fields, and that the two possible choices are the two horns of a dilemma.

**P1 -- the three-index family, and the embedding works.** Fields keyed by the tower's own
coordinate towers:

    type ET.Base<-v: R.Rat> is Data:
      EBase{r: R.Rat}

    type ET.Ext<-A: Data, -B: Data, -D: Data> is Data:
      EExt{u: A, w: B}

    def ET(t: T.Tower) -> Data:
      match t:
        case T.Base{v}:
          ET.Base<v>
        case T.Ext{re, im, d}:
          ET.Ext<ET(re), ET(im), ET(d)>

    def ET.of(+t: T.Tower) -> ET(t):
      match t:
        case T.Base{v}:
          EBase{v}
        case T.Ext{re, im, d}:
          EExt{ET.of(re), ET.of(im)}

    def ET.add(+t: T.Tower, x: ET(t), y: ET(t)) -> ET(t):
      match t:
        case T.Base{v}:
          EBase{+a} = x
          EBase{+b} = y
          EBase{R.Rat.add(a, b)}
        case T.Ext{re, im, d}:
          EExt{+u1, +w1} = x
          EExt{+u2, +w2} = y
          EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)}

    law ET.add.comm:
      for +t: T.Tower
      for +x: ET(t)
      for +y: ET(t)
      {ET.add(t, x, y) == ET.add(t, y, x) : ET(t)}

    Error: 241 TODOs found.

241 = the 240 of src/tower.bend (229 of rat plus its eleven) plus the one unfilled law,
so every definition typechecks and the statement is legal. `ET.add` recurses on the
coordinate towers and takes no radicand parameter at all. Note what this statement is:
a ring law at a *variable* tower level with *no* agreement hypothesis -- exactly what the
carrying design could not state, since `add.comm` is false there (round twenty-five P5).

**P2 -- fields keyed by the radicand, and the embedding fails as before.**

    type ET2.Ext<-A: Data, -B: Data, -D: Data> is Data:
      E2Ext{u: D, w: D}

    def ET2.of(+t: T.Tower) -> ET2(t):
      match t:
        case T.Base{v}:
          E2Base{v}
        case T.Ext{re, im, d}:
          E2Ext{ET2.of(re), ET2.of(im)}

    Error:
    - expected : ET2(d)
    - observed : ET2(re)
    Context:
    - re : src/tower.Tower
    - im : src/tower.Tower
    - d  : src/tower.Tower
    Location: ET2.of

Both coordinates in the ring at the radicand's level is what arithmetic needs; it is also
what makes the embedding unprovable.

**P3 -- and P1's family cannot multiply.** `mul` on it, with the honest formula
(`u1*u2 + (w1*w2)*d` and `u1*w2 + w1*u2`):

    Error:
    - expected : probe.tower.e1.ET(re)
    - observed : probe.tower.e1.ET(im)
    Context:
    - u1 : probe.tower.e1.ET(re)
    - w1 : probe.tower.e1.ET(im)
    - u2 : probe.tower.e1.ET(re)
    - w2 : probe.tower.e1.ET(im)
    Location: E.ET.mul

The failure is the cross-coordinate product `w1 * w2`, at index `ET(im)` where `ET(re)` is
wanted -- not the radicand term. Multiplying across the two coordinates needs them keyed
by one type, and that is precisely the indexing P2 rules out.

**Why this is structural rather than fixable.** A tower `Ext{re, im, d}` has three
separate tower fields at the same level, with no shared index, and bend offers no way to
state that they are at the same level: `Tower.depth` is a function returning a Nat, not a
type index, and there is no equality on types to transport an element along. The checker
can therefore never see `ET(re) = ET(d)`. The typed route must give up the embedding or
the arithmetic, and route A's untyped tower -- where everything is one type -- is what
makes the arithmetic possible in the first place. Consequence for the user's goal: the
level and radicand discipline cannot be enforced by types in bend as it stands; it has to
be carried by proofs, for which Step 1's machinery already exists and is already indexed
by dependent tower indices (`type Tower.Wf.Ext<-re: Tower, -im: Tower, -d: Tower>` with
fields `Tower.wf(re)`, `Tower.wf(im)`, `Tower.wf(d)`).

The constructive residue: the `ET` family is a sound base for the radicand-free part of
the ring. `add`, `neg` and their laws are stateable at a variable level with no
hypothesis, and the statement in P1 is the first such law measured in bend. Its fill is
the obvious next unit. `mul` is the operation that needs the radicand to cross a level,
and it is the one the typed route cannot have.

## Round twenty-eight -- The fill lands: a hypothesis-free ring law proved at a variable tower level

Round twenty-seven showed the statement is legal on the three-index `ET` family
(`def ET(t: T.Tower) -> Data` returning `ET.Ext<ET(re), ET(im), ET(d)>` for
`T.Ext{re, im, d}`). The question was whether it is provable. It is, with the
`Rat.add_comm` recipe unchanged: `match t`, destructure both operands, one `Equal.cong`
per coordinate, `Equal.trans` with the middle endpoint spelled out.

    def ET.add.comm(t, x, y):
      match t:
        case T.Base{v}:
          EBase{+a} = x
          EBase{+b} = y
          Equal.cong(R.Rat, ET.Base<v>, u => EBase{u},
            R.Rat.add(a, b), R.Rat.add(b, a), R.Rat.add_comm(a, b))
        case T.Ext{re, im, d}:
          EExt{+u1, +w1} = x
          EExt{+u2, +w2} = y
          Equal.trans(ET.Ext<ET(re), ET(im), ET(d)>,
            EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)},
            EExt{ET.add(re, u2, u1), ET.add(im, w1, w2)},
            EExt{ET.add(re, u2, u1), ET.add(im, w2, w1)},
            Equal.cong(ET(re), ET.Ext<ET(re), ET(im), ET(d)>,
              u => EExt{u, ET.add(im, w1, w2)},
              ET.add(re, u1, u2), ET.add(re, u2, u1), ET.add.comm(re, u1, u2)),
            Equal.cong(ET(im), ET.Ext<ET(re), ET(im), ET(d)>,
              u => EExt{ET.add(re, u2, u1), u},
              ET.add(im, w1, w2), ET.add(im, w2, w1), ET.add.comm(im, w1, w2)))

**Evidence, by count.** With the fill: `Error: 11 TODOs found.` -- `tower.bend`'s eleven
laws, since rat's 229 are filled by the rat_proofs import and mine is filled by the
definition above. Round twenty-seven's unfilled version of the same file read 241
(240 + my law), so an unattached fill here would read 12.

**Negative control.** Returning the first `Equal.cong` alone, without the `Equal.trans`
wrapper, is rejected -- as a type error on the unmatched endpoint, not a syntax error:

    Error:    - expected : {EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)} == EExt{ET.add(re, u2, u1), ET.add(im, w2, w1)} : ET.Ext<ET(re), ET(im), ET(d)>}    - observed : {EExt{ET.add(re, u1, u2), ET.add(im, w1, w2)} == EExt{ET.add(re, u2, u1), ET.add(im, w1, w2)} : ET.Ext<ET(re), ET(im), ET(d)>}    Context:    - re : src/tower.Tower    - im : src/tower.Tower    - d  : src/tower.Tower    - u1 : ET(re)

**The direct form suffices.** A variant routing the injected element through a
declared-return-type helper (`def ET.Ext.at(+re: T.Tower, +im: T.Tower, +d: T.Tower,
u: ET(re), w: ET(im)) -> ET.Ext<ET(re), ET(im), ET(d)>`) and spelling all three `trans`
endpoints through it also gives 11. This matches round twenty-four: on indexed types the
`%`-ascriptions are what fail, and direct terms avoid the wall.

**What it means.** The radicand-free half of the ring is fully available typed: `add` at a
variable tower level has a law with no agreement hypothesis, stated and proved, and `neg`
follows the same recipe. `mul` still cannot be written (round twenty-seven P3), since it
is the operation that needs the radicand to cross between levels. The plan is unchanged --
route A for the arithmetic, `Tower.wf` evidence for the discipline -- with the `ET` base
as an asset if a hybrid is ever wanted.

## Round twenty-nine -- The witnessed route A has no teething: evidence is inert, and the mismatch value is indistinguishable

Round twenty-seven said the level and radicand discipline would have to be carried by
proofs, with Step 1's `Tower.wf` evidence as the machinery. Three probes say it cannot.

**P1 -- matching the evidence first.** With `wx` evidence about `x`:

    def T.Tower.head(+x: T.Tower, wx: T.Tower.wf(x)) -> T.Tower:
      match wx:
        case T.WfExt{wfre, wfim, wfd}:
          match x:
            case T.Ext{re, im, d}:
              re
        case T.TowerOk{}:
          match x:
            case T.Base{v}:
              x

    Error:
    - message  : a match on a parameter or field (this name is a def or a consumed binder:
                 give the value its own def)
    Location:
     8 |     case T.WfExt{wfre, wfim, wfd}:
     9>|       match x:

**P2 -- the natural ordering.** Match the tower first, so the evidence should reduce, then
match the evidence:

    def T.Tower.addW(+d: T.Tower, x: T.Tower, wx: T.Tower.wf(x),
                     y: T.Tower, wy: T.Tower.wf(y)) -> T.Tower:
      match x y:
        case T.Base{a} T.Base{b}:
          match wx wy:
            case T.TowerOk{} T.TowerOk{}:
              T.Base{R.Rat.add(a, b)}
        ...

    Error:
    - message  : a match on a parameter or field (this name is a def or a consumed binder:
                 give the value its own def)
    Location:
     9 |     case T.Base{a} T.Base{b}:
    10>|       match wx wy:

Same message, same obstruction. The mechanism is the stuck-term wall: the scrutinee's type
`Tower.wf(x)` does not reduce for a variable `x`, so the evidence is inert. It is accepted
as a parameter, and a law may quantify it -- `law T.Tower.depth.refl: for +x: T.Tower; for
+wx: T.Tower.wf(x)` reports `Error: 241 TODOs found.` = tower.bend's 240 plus one, so the
statement is legal -- but it can never drive a dispatch.

**P3 -- and even if it could, it would not help.** Well-formedness is orthogonal to level
agreement: two towers can both be well-formed and be at different levels. The property that
would matter is "x is at d's level", which is a proof obligation about depth, not a data
witness.

**P4 -- the mismatch value is indistinguishable.** The mixed arms return `Tower.zero(d)`,
whose depth is `1 + depth(d)` by the landed `depth.zero` law -- exactly the depth of a
correct sum at that level. It is a legitimate ring element, so no theorem about *values*
can call it wrong; depth does not separate them and nothing else does.

**P5 -- the absurdity machinery exists.** Surveyed: `law lt_ne_eq: for e: {LT{} == EQ{} :
Cmp}; Empty`, `law gt_ne_eq` (`{GT{} == EQ{} : Cmp}`), `law lt_ne_gt`, `law cmp_eq`, and
`Empty.absurd(-A: Type, e: Empty) -> A`. `Nat.cmp` is a checker built-in (no module prefix;
`N.Nat.cmp` is rejected as a name) and computes on literal zeros, so `cmp(0n, 0n)` is
`EQ{}` and `cmp(1n+k, 0n)` is `GT{}`. **Proved.** The bridging lemma is real, with no laws of its own in the file:
`All terms check.` So the absurdity machinery is available end to end:
`Empty.absurd`, `lt_ne_eq`, `gt_ne_eq`, `Equal.sym`, `Equal.cong`, and `Nat.cmp`
computing on literal zeros.

**Verdict and recommended change.** The only mechanism in bend that removes the
silent-wrong-answer hazard is failing loudly -- a distinguished marker from the mixed arms,
forced to be handled because matching on `Tower` becomes non-exhaustive at every consumer.
Measured cost: 31 match/case sites in `src/tower.bend`, 3 in `src/tower_proofs.bend`, and
no other file in the repo matches on `Base`/`Ext`. That changes the landed public API, so
it is the user's call rather than an autonomous edit; the weaker alternative is to keep the
convention and rely on `depth` invariants at the consumer boundary.

## Round thirty -- Failing loudly is cheap, and it finds a second silent zero

The fail-loud probe was generated from `src/tower.bend` itself: the real type, operations,
helpers and laws, with the change applied textually, so the measurement is of the actual
code rather than a sketch.

**Two markers, two failure modes.** `Bad{}` from the four mixed-shape arms -- two in `add`,
two in `mul` -- and `Fuel{}` from `mul`'s `case 0n:` arm. The second is a finding about
landed code: `mul` is fuel-driven, and an exhausted fuel returned `Tower.zero(d)`, a
plausible zero decided by a caller-supplied Nat. The plan listed a fuel-sufficiency law as
Step 2's business but not that the failure was silent; with two markers the fuel law becomes
that marker's unreachability statement.

**The checker walks the definitions.** It reports `expected : cases for Bad, Fuel` one at a
time -- at `Tower.zero`, then `Tower.add`, then `Tower.neg`, then the proof helper
`Tower.wf.zero`. Eight sites needed arms in all: `depth`, `zero`, `add`, `neg`, `mul`,
`one`, `wf`, and `wf.zero`. Since `wf.zero`'s result type is `Tower.wf(Tower.zero(t))` and
`wf(Bad{})` is `Tower.Ok`, its arms are evidence (`TowerOk{}`) rather than markers.
`Tower.wf.lift` needed no change.

**Wildcards bound the cost.** A binary match over two Towers would otherwise need sixteen
combinations. bend has wildcard patterns -- a minimal probe with

    def W.k(x: W, y: W) -> Nat:
      match x y:
        case WA{} WA{}:
          0n
        case _ _:
          1n

prints `All terms check.` -- so `add` keeps its two matching arms plus `case _ _: Bad{}`,
and `mul` uses `Fuel{} _`, `_ Fuel{}`, `_ _` so a marker operand propagates its own
diagnosis instead of being flattened into `Bad`.

**What the file's output says.** With the change applied the probe checks: its only output
is a TODO count, no error at all, so every definition, both helper proofs and all eleven
copied law statements stay legal. The count is 111 with this import set, and it is exactly explained: nat contributes
129 laws and nat_proofs fills every one of them, so a control probe importing nat,
nat_proofs and rat with no laws of its own reports 100 -- rat's 229 minus nat's 129 --
and the probe's eleven copied laws bring it to 111. src/tower.bend alone reports
240 = rat's 229 plus its own eleven. So the number tracks unfilled laws in the import
graph and nothing about the change. What this does not
measure: the fills live in `src/tower_proofs.bend` and were not copied into the probe, so
the laws' *truth* under the change is untested -- only their statements' legality and the
operations' typechecking.

**The unreachability proof works end to end.** `Tower.tag` (`Base`/`Ext` to `0n`, `Bad` to
`1n`, `Fuel` to `2n`) is the discriminator; with round twenty-nine's absurdity lemma
(`0n == 1n+k` implies `Empty`) one case is proved:

    def Tower.bb.not.bad(+d: Tower, +v: R.Rat, +w: R.Rat,
        e: {Tower.add(d, Base{v}, Base{w}) == Bad{} : Tower}) -> Empty:
      Empty.absurd(Empty, N.Nat.succ_ne_zero(0n,
        Equal.cong(Tower, Nat, u => Tower.tag(u),
          Tower.add(d, Base{v}, Base{w}), Bad{}, e)))

The full theorem is four cases of that shape and carries an equal-depth hypothesis, which is
what makes the mixed cases absurd. It certifies "same-level inputs never see the marker";
the discipline of passing same-level operands stays a caller obligation.

## Round thirty-two -- The safety theorems land: clean in, clean out

Two laws now prove that the markers of round thirty-one are unreachable for correct
callers, and both are filled.

**The predicate.** `Tower.clean(t) -> Data` returns `Tower.Clean` at a Base,
`Tower.Clean.Ext<re, im, d>` at an Ext, and `Empty` at a marker:

    type Tower.Clean.Ext<-re: Tower, -im: Tower, -d: Tower> is Data:
      CleanExt{cre: Tower.clean(re), cim: Tower.clean(im), cd: Tower.clean(d),
               hri: {Tower.depth(re) == Tower.depth(im) : Nat}}

    def Tower.clean(t: Tower) -> Data:
      match t:
        case Base{v}:   Tower.Clean
        case Ext{re, im, d}: Tower.Clean.Ext<re, im, d>
        case Bad{}:     Empty
        case Fuel{}:    Empty

Since the Ext case demands evidence for its parts recursively, evidence for a computed tower
is a proof that no marker appears anywhere inside it.

**The laws**, both under clean hypotheses for `d`, `x`, `y` and `h: {depth(x) == depth(y)}`:

    law Tower.add.depth: {Tower.depth(Tower.add(d, x, y)) == Tower.depth(x) : Nat}
    law Tower.add.clean: Tower.clean(Tower.add(d, x, y))

**Five things the fills forced.**

1. The predicate had to carry `hri`. The first version had no level relation at all and was
   unprovable: `depth` reads only the re slot, so an Ext/Ext call's im coordinates have no
   depth relation to induct with. This is round twenty-nine's conclusion -- the level
   discipline lives in the evidence -- made concrete.
2. A field relating the coordinates to the radicand is deliberately absent. Nothing relates
   an operand's own radicand to the caller's `d`, and `add` never recurses into `d`, so it
   is neither derivable nor needed.
3. `succ_add_ne`'s instantiated parameter type does not match the natural spelling up to the
   checker's comparison -- observed `{0n == 1n+depth(rx)}`, expected
   `{0n == 1n+Nat.add(depth(rx), 0n)}` -- so the mixed-shape arms use round twenty-nine's
   route: `Nat.cmp` for discrimination plus `eq_ne_gt` and `gt_ne_eq`.
4. The mixed arm's goal type is `{0n == 1n+depth(rx)}`, not reversed: the result there is
   `Bad`, whose depth is `0n`.
5. Linearity: `hd` is used five times in the clean fill's Ext/Ext branch, so it is marked
   `+hd` on the law's `for` list. A fill inherits those marks positionally, which is why the
   fix belongs in the law rather than in the fill's parameter list.

**Each fill is eight arms.** Four shape arms: Base/Base definitional; Ext/Ext the induction,
the re relation recovered by `succ_inj` from the outer hypothesis and the im relation
assembled from the evidence's `hri` fields, with the result's own `hri` built as a two-step
`Equal.trans`; the two mixed arms absurdity from the equal-depth hypothesis. Four marker
arms hand the marker's own evidence to `Empty.absurd` and name their goal type, because
`add(d, Bad{}, y)` does not reduce when `y` is a variable.

**The fuel obligation: statement checked, fill deferred.** With strictly more fuel than the
operands' depth,

    for hf: {Nat.cmp(Tower.depth(x), f) == LT{} : Cmp}
    Tower.clean(Tower.mul(f, d, x, y))

reports 243 TODOs = tower's 242 plus one, so the statement is legal. It was checked in a
throwaway file rather than landed, since an unfilled law leaves the proofs gate red. Its fill
is a nat-inequality induction -- the recursive calls need `depth(rx) < g` from
`1+depth(rx) < 1+g`, which is what the library's `cmp_lt_succ_r` family is for. `neg` and
`one` were left alone under the goal's "if cheap": `neg`'s Ext case needs
`{depth(neg(rx)) == depth(neg(ix))}`, i.e. a depth law for `neg` first.

**Gates.** All six proof files print `All terms check.`; counts nat 129, int 32, qext 34, rat
229, qrat 265, tower 242; `probe.bend` and `probe.payoff.bend` check, `scratch.bend` prints
its inversion triple.

**Scope of the guarantee.** A caller supplying clean operands at equal depth cannot receive a
marker at any depth, so no silent zero enters from a level mismatch or an exhausted fuel. The
hypotheses are obligations bend cannot express as types, so this is a guarantee about correct
callers: pass operands of unequal depth and the result is `Bad`, which the consumer is forced
to handle rather than mistake for a number.

## Round thirty-three -- The fuel obligation splits, and its extension case surfaces the radicand question

**Landed and proved: the base shape.**

    law Tower.mul.fuel.base:
      for +g: Nat
      for +d: Tower
      for a: R.Rat
      for b: R.Rat
      Tower.clean(Tower.mul(1n+g, d, Base{a}, Base{b}))

Fill is `T.CleanOk{}`: the successor arm takes the Base/Base branch and returns
`Base{Rat.mul(a, b)}`. Tower's count goes 242 to 243.

**Blocked: the extension shape, and not by fuel arithmetic.** The statement that mirrors
`add.clean` -- clean operands, equal depth, `hrd: {depth(x) == 1n + depth(d)}`, and
`hf: {Nat.cmp(depth(x), f) == LT{}}` -- cannot support its own recursion. `mul`'s Ext/Ext arm
calls `mul(g, d, rx, ry)` at the level below x, and the caller's `hrd` gives, after
cancellation, `depth(rx) == depth(d)`: `rx` and `d` are siblings. The sub-level call would
need a relation one level further down that the statement does not supply. Measured directly:

    def T.Tower.hrd.down(+d: T.Tower, +rx: T.Tower, +ix: T.Tower, +dx: T.Tower,
        hrd: {T.Tower.depth(T.Ext{rx, ix, dx}) == Nat.add(1n, T.Tower.depth(d)) : Nat})
      -> {T.Tower.depth(rx) == Nat.add(1n, T.Tower.depth(d)) : Nat}:
      N.succ_inj(T.Tower.depth(rx), T.Tower.depth(d), hrd)

    Error:
    - expected : {src/tower.Tower.depth(rx) == 1n+src/tower.Tower.depth(d) : Nat}
    - observed : {src/tower.Tower.depth(rx) == src/tower.Tower.depth(d) : Nat}
    Context:
    - hrd : {1n+src/tower.Tower.depth(rx) == 1n+src/tower.Tower.depth(d) : Nat}
    Location: T.Tower.hrd.down

Three distinct claims, kept apart:

1. Measured: the needed hypothesis is not derivable from the caller's.
2. Reasoned, not measured: a sub-level multiplication's radicand is the sub-level's own, not
   `d`. `mul` threads `d` unchanged through every recursive call, so from depth two up the
   `sqrt(d) * sqrt(d) = d` term multiplies by the caller's radicand. That is the radicand-chain
   wall of rounds twenty-six and twenty-seven appearing in the untyped design -- and there it
   was a typing obstruction, whereas here it is a question about values.
3. Untested: whether `mul`'s values are wrong for nested towers at all. A proof obstruction is
   not a semantics proof; the statement I chose may be the wrong shape. The next unit tests it
   numerically -- two depth-2 towers with rational coefficients, product known by hand,
   compared against the printed value the way `scratch.bend` checks the inversion triple.

Until then `mul` is verified for depth-1 towers only. If the threading changes, `mul.ext`'s
statement and the fuel obligation restate with it.

**Gates after this round.** All six proof files print `All terms check.`; counts nat 129, int
32, qext 34, rat 229, qrat 265, tower 243; `probe.bend` and `probe.payoff.bend` check.

## Round thirty-four -- Depth-2 multiplication was broken, and the markers made it visible

The test the fuel obstruction pointed at, run with real values. Level 1 lives in Q(sqrt 5), a
level-1 tower being `Ext{p, q, Base{5}}`; level 2 extends it by `sqrt(D)` with D the level-1
element 2, so a level-2 element is `Ext{R, I, D}`. The control is `sqrt(5) * sqrt(5)` at level
1; the test is `(sqrt(5) + sqrt(2))^2`, whose true value is `7 + (2*sqrt(5))*sqrt(2)`.

**Before the fix**, printed as control | product | expectation:

    control:   Ext{Base{5}, Base{0}, Base{5}}                                   = 5, correct
    product:   Ext{Ext{Bad{}, Bad{}, D}, Ext{Bad{}, Base{2}, D}, D}             Bad in place of the answer
    expected:  Ext{Base{7}, Ext{Base{0}, Base{2}, Base{5}}, D}

`mul` could not multiply depth-2 elements at all, and the markers are why that was visible:
before round thirty-one the same call returned `Tower.zero(D)`, a plausible element that nothing
downstream would have questioned.

**Diagnosis.** `mul`'s Ext/Ext arm handed the *level-k* radicand to level-(k-1) multiplications,
both as the threaded parameter and, through it, as what the coordinates' own recursions saw. At
depth 2 the coordinates are rationals while D is a level-1 tower, so those operands sat at
different depths and the mixed-shape arm fired.

**The fix** on branch `mul-radicand-threading`:

- `Tower.rad(t)` returns `d` for `Ext{re, im, d}` and `t` for a Base -- the latter a dummy,
  never read, since a Base/Base multiplication takes no radicand. Reading the radicand off the
  operand is what lets the recursion descend without a caller-supplied chain, which is exactly
  what rounds twenty-six and twenty-seven could not do in the typed designs.
- The Ext/Ext arms of `mul` and `add` pass `Tower.rad(...)` in the radicand *slot* of their
  recursive calls. The `sqrt(d)*sqrt(d) = d` term's second operand stays the caller's `d` -- it
  is the level's own radicand and the caller is the one who knows it -- and so does the
  result's third field.
- `add`'s parameters become `(x, y, +d)`: the termination check requires each argument
  unchanged until one shrinks, and `add(Tower.rad(rx), rx, ry)` changed the first before the
  second shrank. Operands first is accepted.
- `add.ext` and `mul.ext` restate to the new unfoldings; `add.base`, `add.depth` and
  `add.clean` reorder their `for` lists. Pattern binders used twice (`rx`, `ix`) take `+`.

**A mistake worth recording.** The first attempt also replaced the `sqrt(d)*sqrt(d) = d` term's
operand with `Tower.rad(rx)`, and the control caught it: `sqrt(5)*sqrt(5)` printed
`Ext{0, 0, 5}` -- zero -- because at level 1 that operand is the rational 5 whereas
`rad(Base{0})` is 0. Reverted, after which the control printed `Ext{5, 0, 5}` again.

**After the fix**, the product prints `Ext{Ext{7, 0, 5}, Ext{0, 2, 5}, Ext{2, 0, 5}}`, identical
to the hand-computed expectation: depth-2 arithmetic is correct.

**Still open.** `src/tower_proofs.bend` is red on the branch until its fills follow the new
signatures. The parameter orders are mechanical; `add.clean`'s Ext/Ext arm additionally needs
clean evidence for `Tower.rad(rx)`, a function of a variable operand, so the fill has to match
on the coordinates' shape as well. `main` is untouched and the law statements are unchanged
apart from the reordering.

## Round thirty-five -- The radicand fix is verified by a checked gate, and one claim was wrong

**The gate, and the correction.** Round thirty-four said the fixed product was "identical to the
hand-computed expectation, element for element". The printing showed the values agreeing, but the
first coordinate's *form* differed, and I did not look closely enough. The product's is

    Ext{Base{7}, Base{0}, Base{5}}          -- 7 as a level-1 element

while my expectation used `Base{7}`, a level-0 tower. Same number, different depth. The checker's
equality is structural, so when the test became a gate rather than a printout it rejected my
expectation:

    Location: mul.depth2.ok
    expected : Ext{Ext{Base{7},Base{0},Base{5}}, Ext{Base{0},Base{2},Base{5}}, D}
    observed : Ext{Base{7}, Ext{Base{0},Base{2},Base{5}}, D}

The code was right and the expectation was malformed: a coefficient of a level-2 element sits at
the radicand's level, so 7 there is the level-1 element `7 + 0*sqrt(5)`. With the expectation
rewritten in that form both defs check:

    def mul.depth1.ok() -> {ctrl1() == want1() : T.Tower}:  {==}
    def mul.depth2.ok() -> {test2() == want2() : T.Tower}:  {==}
    All terms check.

`probe.tower.depth.bend` is now a tracked gate, and it is stronger than the printout was: the
equalties are decided by the checker, so the file cannot pass on values that only look alike.

**The fills.** Two things made them mechanical.

`TowerCleanRad` transports clean evidence to a level's radicand:

    def TowerCleanRad(t: T.Tower, h: T.Tower.clean(t)) -> T.Tower.clean(T.Tower.rad(t)):
      match t:
        case T.Base{v}: h
        case T.Ext{re, im, d}: T.CleanExt{+cr, +ci, +cd, +hri} = h; cd
        case T.Bad{}: h
        case T.Fuel{}: h

The radicand is a *part* of the operand -- its third field at an Ext, the operand itself at a
Base -- so the operand's evidence already contains the radicand's, and the fills need no new
hypothesis for the sub-level radicand. Same pattern as `Tower.wf.zero`: evidence transports,
equations do not.

And a naming rule, measured: a helper declared *in* a proofs file must not carry another
module's prefix. `def T.Tower.clean.rad(...)` in `tower_proofs.bend` resolves as a def in the
module aliased `T`, i.e. `tower.bend`, and a second importing file reports `expected : a defined
name / observed : src/tower.Tower.clean.rad`. Unqualified is the pattern the nat proofs use with
`NatIsPos`.

The rest is mechanical: `add.base`, `add.ext`, `add.depth`, `add.clean` reorder their parameter
lists to the new signatures and their inner call sites follow, passing `Tower.rad(rx)` in the
radicand slot and `TowerCleanRad(rx, hxr)` for its evidence.

**Gates.** All six proof files print `All terms check.`; counts nat 129, int 32, qext 34, rat 229,
qrat 265, tower 243; `probe.bend` and `probe.payoff.bend` check; `scratch.bend` prints its
inversion triple; `probe.tower.depth.bend` is new and green.

**Still open.** The fuel obligation's extension statement was checked in round thirty-three but
never landed, and its fill was blocked by exactly the hypothesis this round removed -- the
recursion no longer needs a relation between the coordinates and the caller's radicand. What
remains is the fuel-inequality induction: `cmp(1+depth(rx), 1+g) == LT{}` to
`cmp(depth(rx), g) == LT{}`, the library's `cmp_lt_succ_r` family. `main` is untouched.

## Round thirty-six -- The fuel obligation narrowed to one missing law

**Landed.** `law Tower.mul.fuel.zero: {Tower.mul(0n, d, x, y) == Fuel{} : Tower}`, filled `{==}`.
`mul`'s first arm is `case 0n: Fuel{}`, so fuel zero is the failure case for every pair of
operands, markers included. Tower's count goes 243 to 244, and the proofs gate stays green.

**The induction step needs no lemma.** Stripping the successor from `cmp(1+a, 1+b)` looks like it
should need a cancellation law; `cmp_lt_succ_r` is the wrong direction (it weakens `a < b` to
`a < 1+b`). It is not needed at all: `Nat.cmp` is a checker built-in that computes on structure,
so `cmp(1+depth(rx), 1+g)` reduces to `cmp(depth(rx), g)` and the recursive call's fuel bound is
exactly the caller's hypothesis. The library's own `cmp_eq` fill relies on the same reduction,
which is where the expectation comes from; the fill will confirm it.

**One law is missing: `Tower.mul.depth`.** In `mul`'s Ext/Ext arm the second recursive call
takes an operand that is itself a result,

    Tower.mul(g, Tower.rad(rx), Tower.mul(g, Tower.rad(rx), ix, iy), d)

so its fuel bound needs `depth(mul(g, rad(rx), ix, iy)) == depth(ix)` -- a depth law for `mul`,
the analogue of the landed `add.depth`. That law is an induction whose Ext/Ext arm combines the
two recursive depth facts through `add.depth` (which wants the coordinates' depths to agree, and
the evidence's `hri` fields plus the equal-depth hypothesis provide that). With it in place,
`mul.fuel.ext` follows with the level-discipline hypothesis

    for hrd: {Tower.depth(x) == Nat.add(1n, Tower.depth(d)) : Nat}

which the `sqrt(d)*sqrt(d) = d` term needs, since that term multiplies by `d` and `d`'s depth has
to match the coordinates'.

Nothing about the radicand chain blocks either law now. That is what the threading fix bought:
round thirty-three measured the same obligation as blocked because the recursion needed a
relation the caller's hypotheses could not give, and now the radicand is read off the operand
instead.

**One thing tried and rejected.** I expected the `hrd` hypothesis to be droppable -- that
`depth(x) == 1n + depth(rad(x))` would hold by reduction once the shape is known. It does not:

    def hrd.refl(+re: T.Tower, +im: T.Tower, +d: T.Tower)
      -> {T.Tower.depth(T.Ext{re, im, d})
          == Nat.add(1n, T.Tower.depth(T.Tower.rad(T.Ext{re, im, d}))) : Nat}:
      {==}

    Error:
    - expected : 1n+src/tower.Tower.depth(re)
    - observed : 1n+src/tower.Tower.depth(d)
    Location: hrd.refl

`depth` unfolds from the *first* field, `rad` returns the *third*, so the relation is
`{1n + depth(re) == 1n + depth(d)}`: the level discipline itself, a property of a well-formed
tower rather than a reduction. So `hrd` stays a hypothesis -- which is what rounds twenty-nine and
thirty-three concluded before I briefly thought it could be avoided.

## Round thirty-seven -- `mul.depth` needs the level discipline in the evidence

Attempting the depth law for `mul` exposed what its recursion needs, and the measurement is
precise. The recursion hands the next call an Ext's own coordinate, so the relation it must pass
is about that coordinate: `depth(rx) == 1n + depth(rad(rx))`, which at `rx = Ext{p, q, r}` unfolds
to `depth(p) == depth(r)`. What `Tower.Clean.Ext` carries is `hri`, that the two *coordinates*
agree:

    def T.Tower.level.from.clean(+re: T.Tower, +im: T.Tower, +d: T.Tower,
        h: T.Tower.clean(T.Ext{re, im, d}))
      -> {T.Tower.depth(re) == T.Tower.depth(d) : Nat}:
      T.CleanExt{+cr, +ci, +cd, +hri} = h
      hri

    Error:
    - expected : {src/tower.Tower.depth(re) == src/tower.Tower.depth(d) : Nat}
    - observed : {src/tower.Tower.depth(re) == src/tower.Tower.depth(im) : Nat}
    Context:
    - cr : src/tower.Tower.clean(re)
    - ci : src/tower.Tower.clean(im)
    - cd : src/tower.Tower.clean(d)
    Location: T.Tower.level.from.clean

So `clean`, being a marker predicate, implies nothing about levels -- `cd` is `clean(d)`, not a
depth relation -- and the relation the recursion needs is about a sub-tower of an operand, which
only that operand's evidence knows.

**Recommendation: put the discipline in the evidence.** `Tower.Clean.Ext` gains
`hrd: {Tower.depth(re) == Tower.depth(d) : Nat}`. The alternative -- a hypothesis on each law
that needs it -- fails for a recursion, because the hypothesis would have to be guessed per
recursive call while callers cannot produce relations about sub-towers they cannot see; the
evidence is built once per tower and transports. Round thirty-two removed `hrd` as "neither
derivable nor needed": true of `add`, whose recursion never touches the radicand, false of `mul`,
whose `sqrt(d)*sqrt(d) = d` term does.

**The cost, up front.** The two landed safety laws gain a caller-side discipline hypothesis, and
their fills construct their result's `hrd` from the operand's. That means `add`'s result is
well-formed only when the caller passed the level's own radicand -- which is the discipline -- and
it is the side-condition threading Step 1 flagged as the risk of the wf design. It is also the
last piece `mul.depth` and `mul.fuel.ext` need.

## Round thirty-eight -- The evidence change is cheap, and the radicand parameter is unnecessary

**Blast radius, measured rather than estimated.** Adding `hrd` to `Tower.Clean.Ext` and
re-checking:

- `src/tower.bend`: 244 TODOs, unchanged. The type change is legal by itself, because the law
  statements name `Tower.clean(...)` and not its fields.
- `src/tower_proofs.bend`: one error, mechanical --

    - message : a tower.CleanExt pattern with 5 fields
    Location: TowerCleanRad
    98>|       T.CleanExt{+cr, +ci, +cd, +hri} = h

The change was then reverted, so the branch stays green while the design is settled.

**The parameter is the problem.** A constructed result cannot supply `hrd` only because its
radicand may be the *caller's* `d` instead of the operand's own `dx`, and nothing relates those
two -- nor can anything, since a caller may pass any tower. But the radicand a multiplication
needs is a property of the operand: `Ext{re, im, d}` already stores it. Dropping the parameter
removes the disagreement instead of assuming it away:

    def Tower.add(x: Tower, y: Tower) -> Tower
      # Ext/Ext arm: Ext{Tower.add(rx, ry), Tower.add(ix, iy), dx}
    def Tower.mul(+f: Nat, x: Tower, y: Tower) -> Tower
      # Ext/Ext arm reads dx for the sqrt(d)*sqrt(d) = d term, and recurses on operands

Every radicand then comes from an operand's own third field, so each level's radicand is
intrinsic and no caller-side discipline hypothesis is needed -- there is nothing left for a
caller to get wrong about `d` because there is no `d`. `Tower.rad` becomes unused, its callers
having become destructuring. The safety laws keep their shape, with `hd` replaced by the result's
`cd`, taken straight from the operand's evidence.

The cost is the same shape as the previous restatement: four `add` laws, the `mul` laws, the
fills, and the depth gate's calls. That is the difference between "`add`'s result is well-formed
only when the caller passed the right radicand" and "`add`'s result is well-formed".

## Round thirty-nine -- The radicand is intrinsic to the operand, and the side condition is gone

Landed on `radicand-intrinsic`, cut from `mul-radicand-threading` so that branch stays mergeable on
its own.

**Signatures.** `Tower.add(x, y)` and `Tower.mul(+f, x, y)`. The radicand is a parameter nowhere:
each arm reads it from the operand in hand, an Ext's third field, so `Tower.rad` and the evidence
transport helper are deleted -- their callers became destructuring.

**The evidence carries the discipline, and the field is free.** `Tower.Clean.Ext` gains
`hrd: {Tower.depth(re) == Tower.depth(d) : Nat}`. The measured cost matched round thirty-eight's
estimate exactly: `tower.bend` stayed at 244 TODOs (its law statements name `Tower.clean(...)`,
not the fields), the fills needed one pattern arity, and the field's *value* costs nothing. In
`add.clean`'s Ext/Ext arm the result is `Ext{Tower.add(rx, ry), Tower.add(ix, iy), dx}`, whose
third field is the operand's own `dx`, so `cd` is the operand evidence's field and `hrd` is a
two-step `Equal.trans` through `add.depth`:

    T.CleanExt{cr, ci, hxd, <hri chain>,
      Equal.trans(Nat, T.Tower.depth(T.Tower.add(rx, ry)),
        T.Tower.depth(rx), T.Tower.depth(dx), dr, hxrd)}

**The side condition vanished with the parameter.** Both safety laws keep their shape --
`for +x, +y, hx: Tower.clean(x), hy: Tower.clean(y), h: {Tower.depth(x) == Tower.depth(y)}` -- and
`hd` is simply gone rather than replaced by something stricter. Round thirty-seven's tradeoff,
"`add`'s result is well-formed only when the caller passed the right radicand", does not arise:
there is no radicand for a caller to get wrong. The depth gate got stronger for the same reason --
`(sqrt(5) + sqrt(2))^2` is now checked with no radicand argument.

**Gates.** All six proof files `All terms check.`; counts nat 129, int 32, qext 34, rat 229, qrat
265, tower 244; `probe.bend`, `probe.payoff.bend`, `probe.tower.depth.bend` check; `scratch.bend`
prints its inversion triple.

**Remaining.** `Tower.mul.depth`, then `Tower.mul.fuel.ext`. Both wanted the level relation that
now lives in the operand's evidence: `mul.depth`'s recursive call needs
`{depth(rx) == 1n + depth(rad(rx))}`, which at an Ext is `hxr.hrd` composed with the shape, with no
law carrying it.

## Round forty -- `add.depth` loses its cleanliness hypotheses, and the chain shortens

`Tower.add.depth` is now

    law Tower.add.depth:
      for +x: Tower
      for +y: Tower
      for h: {Tower.depth(x) == Tower.depth(y) : Nat}
      {Tower.depth(Tower.add(x, y)) == Tower.depth(x) : Nat}

Its old fill got the marker arms' `Empty` witness from `hx` and `hy`. Spelling all sixteen shape
arms out instead: twelve are definitional -- `(Base, Base)`, `(Base, Ext)`, `(Base, Bad)`,
`(Base, Fuel)`, and every pair of markers, all reducing to `{0n == 0n}` -- and four read the
equal-depth hypothesis: the `(Ext, Ext)` induction by `succ_inj` and `cong`, and `(Ext, Base)`,
`(Ext, Bad)`, `(Ext, Fuel)` through `Nat.cmp` and `gt_ne_eq`.

**Why this was worth doing.** `mul.depth`'s fill must call `add.depth` on *products of
coordinates*:

    Tower.add(Tower.mul(g, rx, ry), Tower.mul(g, Tower.mul(g, ix, iy), dx))

With cleanliness as a hypothesis that call needs clean evidence for both products, which is a
whole separate safety law for `mul` -- `mul.clean` -- before `mul.depth` can be written at all.
Without it, the remaining chain is two laws: `Tower.mul.depth`, then `Tower.mul.fuel.ext`.

The single caller affected was `add.clean`'s fill, whose two `add.depth` calls had been passing
`hxr, hyr` and `hxi, hyi`. Those arguments are gone.

**Gates.** All six proof files `All terms check.`; counts nat 129, int 32, qext 34, rat 229, qrat
265, tower 244; `probe.bend`, `probe.payoff.bend`, `probe.tower.depth.bend` check; `scratch.bend`
prints its inversion triple. Landed on `radicand-intrinsic`.

## Round forty-one -- `mul.depth`'s Ext/Ext bookkeeping is verified

The last thing about the depth law that could not be settled by reasoning was the assembly inside
its Ext/Ext arm. It is checked now, in `probe.tower.mul.depth.arm.bend`, which assumes the three
recursive facts and proves the rest:

    def T.Tower.mul.depth.arm(+g: Nat, +rx, +ix, +dx, +ry, +iy, +dy: T.Tower,
        hi: {T.depth(ix) == T.depth(rx) : Nat},
        +hc1: {T.depth(T.mul(g, rx, ry)) == T.depth(rx) : Nat},
        hci: {T.depth(T.mul(g, ix, iy)) == T.depth(ix) : Nat},
        hc2: {T.depth(T.mul(g, T.mul(g, ix, iy), dx)) == T.depth(T.mul(g, ix, iy)) : Nat})
      -> {T.depth(T.mul(Nat.add(1n, g), T.Ext{rx, ix, dx}, T.Ext{ry, iy, dy}))
          == T.depth(T.Ext{rx, ix, dx}) : Nat}:
      ...

      All terms check.

The argument: `mul(1n+g, Ext{rx, ix, dx}, Ext{ry, iy, dy})` unfolds to
`Ext{add(M1, M2), ..., dx}` with `M1 = mul(g, rx, ry)` and `M2 = mul(g, mul(g, ix, iy), dx)`, so
its depth is `1n + depth(add(M1, M2))` against a right-hand side of `1n + depth(rx)`. What must
hold is `depth(add(M1, M2)) == depth(rx)`: chain `depth(mul(g, ix, iy)) == depth(rx)` from `hci`
and `hi`, then `depth(M1) == depth(M2)` from `hc1`, that chain and `hc2` with two `Equal.sym`s,
then `add.depth(M1, M2, ...)` -- callable with only the depth hypothesis since round forty --
and a final `cong` under `u => 1n + u`.

Three slips, all caught by the checker and all mine: a chain whose middle step needed the
evidence relation rather than a product fact; `hc2` passed in the wrong direction; and `hc1` used
three times without its `+` mark.

**The full fill is now assembly**, with nothing unknown left: the three recursive facts above, the
evidence relations each recursive call needs (`hri` chains and `hrd`), the fuel hypothesis
reducing for free from `cmp(1n+a, 1n+g) == LT{}` to `cmp(a, g) == LT{}`, twenty arms (four fuel
zero, sixteen paired shapes, four substantive), and this assembly in the `(Ext, Ext)` one.

## Round forty-two -- The last dependency, and a correction

Assembling `mul.depth` found the piece that is still missing, and it is not the bookkeeping that
round forty-one verified.

`hri` and `hrd` live only inside `Tower.Clean.Ext`, so a law whose proof needs the level relations
must take clean evidence as a hypothesis. For `mul.depth`'s own operands that is fine -- the
caller supplies it -- but its second recursive call is

    Tower.mul(g, Tower.mul(g, ix, iy), dx)

and its first operand is a *product*. Proving that call needs `clean(mul(g, ix, iy))`, which is a
conclusion no depth law produces. That is `Tower.mul.clean`, and round forty's claim that the
remaining chain was two laws was wrong: removing `add.depth`'s cleanliness hypotheses helped, but
it was a different requirement from this one.

**Why the path is still finite: `mul.clean` is provable.** Its Ext/Ext arm needs evidence for
`(ix, iy)`, for `dx`, and for `mul(g, ix, iy)`. The first two come out of the operand's own
evidence -- `cre`/`cim` and `cd` -- and the third is the conclusion of its own recursive call, so
nothing new has to be assumed. The order is therefore

    Tower.mul.clean  ->  Tower.mul.depth  ->  Tower.mul.fuel.ext

with `mul.clean` shaped like the landed `add.clean`, `mul.depth`'s Ext/Ext arm already checked in
`probe.tower.mul.depth.arm.bend`, and `mul.fuel.ext`'s statement checked since round thirty-three.

**State at the end of the round budget.** `radicand-intrinsic` @ `7a5253b` plus this record; all
six proof files `All terms check.`, counts 129/32/34/229/265/244, the three consumer gates and
both tower gates green; `main` untouched at `5dd79dc`. The measurement, the threading fix, its
checked gate, and the intrinsic-radicand redesign are all landed; the fuel obligation has two of
its three facts landed and the third's recipe pinned down to the hypothesis.

## Round forty-three -- The int split, piloted: three tiers, and no consumer count moves

The three-tier split, piloted on `Int` on branch `three-tier-split` (off
`radicand-intrinsic` @ `2619b40`, `main` untouched).

**The convention.** `src/<lib>.bend` is the readable layer (types, operations,
the laws a reader needs). `src/<lib>_helpers.bend` holds the helper laws ---
sign/direction/spelling variants, rearrangements, structural plumbing. The fills
stay in `src/<lib>_proofs.bend`, which fills both tiers. The import only goes one
way: `<lib>_helpers.bend` imports `<lib>.bend`, because a helper law is stated
over the readable layer's types and operations; `<lib>.bend` does not import its
helpers, so a reader of the readable layer never sees them. A consumer that wants
the whole surface imports both (`import ./<lib>_helpers.bend as <alias>H`).

**Why the one-way import is forced.** The obvious shape --- `<lib>.bend` imports
its helpers, so that importing the readable file brings the whole surface --- is
impossible: the helper laws mention `Int` and `Int.mul`, which are defined in
`int.bend`, so the helper file must import `int.bend`. Importing both ways would
be a cycle. The helper layer therefore sits *above* the readable layer, not below
it, and the consumer pays one extra import line.

**The boundary for Int (19 readable / 13 helpers).** Readable: `add_comm`,
`add_assoc`, `add_zero`, `zero_add`, `neg_invol`, `neg_add`, `neg_mul`,
`sub_eq_add_neg`, `mul_comm`, `mul_assoc`, `mul_distrib`, `mul_add_left`,
`mul_zero`, `mul_one`, `one_mul`, plus the canonical-form interface `canon.pos`,
`canon.neg`, `canon.eqv.fwd`, `canon.eqv.bwd`. Helpers: `add_exchange`,
`mul_assoc.pos`, `mul_assoc.neg`, `mul_swap`, `mul_scale`, `scale.pair`,
`scale.cancel`, `scale_cross`, `canon.idem`, `canon.scale`, `canon.scale.go`,
`eq.pos`, `eq.neg`. The rule of thumb applied: a law is readable if it says
something a user of the layer would want to know; it is a helper if it exists to
make a proof go through (a sign split, a mirrored direction, a rearrangement, a
canonical-form step).

**The mechanics, measured.** A fill attaches to a law by its qualified name:
`def I.Int.mul_swap(...)` fills `I.Int.mul_swap`. So moving a law re-aliases its
fill declaration *and* every call site. The pilot moved 13 law units (each with
its comment block, parsed by walking back over contiguous `#` lines), qualified
the moved statements (`Int.mul` -> `I.Int.mul`; the `law Int.x:` declaration line
itself stays unqualified, since a module declares its own names locally), and
rewrote the qualified references longest-first with a boundary guard --- 85
references in all: 44 in `int_proofs.bend`, 40 in `rat_proofs.bend`, 1 in
`qext_proofs.bend`. Every file importing `int.bend` gained
`import ./int_helpers.bend as IH` (7 files).

**The count invariant, before -> after.** Every proof file and every consumer is
byte-identical; only the split pair changes, and it sums to what was there:

| file | before | after |
|---|---|---|
| `src/int.bend` | 32 | **19** |
| `src/int_helpers.bend` | --- | **32** (19 imported + its own 13) |
| `src/nat.bend` | 129 | 129 |
| `src/qext.bend` | 34 | 34 |
| `src/rat.bend` | 229 | 229 |
| `src/qrat.bend` | 265 | 265 |
| `src/tower.bend` | 244 | 244 |

The intermediate measurement is what shows the invariant is real and not
vacuous: with the helper import missing, `rat.bend` reads 216, `qext.bend` 21 and
`qrat.bend` 252 --- each exactly 13 short. Adding the import restores all three.

**Gates.** All six proof files `All terms check.` (the re-aliased fills all
attach --- `int_proofs.bend` was green on the first run after the move);
`probe.bend`, `probe.payoff.bend`, `probe.tower.depth.bend`,
`probe.mul.depth.arm.bend` all check; `scratch.bend` still prints the
`Int{7,0}/2, Int{0,7}/2, Int{0,0}/0` triple.

**Open.** The boundary above is the pilot's proposal, put to the user for review
before it is rolled over nat, rat, qrat, tower and qext. One naming question left
open: `Int.canon.go` is a *def* (the match on the `Nat.cmp` result) and stayed in
the readable file with the other operations, although it is arguably plumbing;
the same question will come back for `Tower.rad` and the `Int.canon` block.

## Round forty-four -- The rest of the split: rat, nat, and two libraries that need no helper file

The pilot's boundary was approved ("Roll it out as proposed"), so the three-tier
convention went over the remaining libraries in order: tower, rat, nat, then the
two small ones.

**Rat: 40 readable, 28 helpers** (`b7e0032`). The helpers are the `Rat.mk`
canonical-form machinery (`mk.scale` and its three coordinate steps,
`mk.canon.go`, `mk.value`, `mk.value.go`, `mk_idem`, `mk_idem.raw`, `mk.rep`,
`mk.trunc`, `mk.diag`), the spelling bridges (`dp.eq.left`, `dp.eq.right`,
`num.mul`, `mk.eqv.raw`, `mk.eqv.val`), the arbitrary-presentation variants of
the readable laws (`add_assoc.arb`, `mul_assoc.arb`, `mul_distrib.arb`,
`mul_add_left.arb`, `neg_add.arb`, the two `.mixed` value laws), `add_exchange`
and the reduced-pair twins `neg.reduced`/`mul.neg_neg.reduced`. The readable
layer keeps the ring laws, the presentation interface a caller actually uses
(`mk.canon`, `mk.fixed`, `mk.zero`, `mk.eqv`, `mk.den.pos`), the value laws
(`add.value`), positivity, the whole division surface and `mul_eq_zero`.

The boundary test that decides the sign splits: `Rat.div.value.gt`/`.lt` stay
readable because there is *no* unqualified `Rat.div.value` for them to be
variants of -- they are the theorems. The same test made `Int.mul_assoc.pos` a
helper (there is a plain `Int.mul_assoc`) and keeps `Rat.mul_inv.gt`/`.lt`
readable.

**Tower: 13 readable, 2 helpers** (`1ba3c1f`). The two helpers are
`Tower.mul.fuel.zero` and `Tower.mul.fuel.base` -- the termination-fuel
obligation, which says nothing about tower values. Two script bugs, both paid
for here:

* The first run duplicated every moved law's declaration line (a mis-indented
  append in the rebuilt `qualify_text`); fixed, after a `git checkout` reset and
  deleting the bad helper file.
* Then a real semantic catch: `Fuel{}` and `Base{a}` in the moved statements
  failed with `expected : a declared constructor (tower.Tower declares
  tower.Base, tower.Ext, tower.Bad, tower.Fuel) / observed : Fuel{}`.
  **Tower's constructors do not carry the type name**, so a moved statement needs
  `T.Fuel{}` and `T.Base{a}` explicitly. Rat/Int/QExt constructors do carry it,
  so qualifying the type covers them -- which is why the same rewrite worked for
  the earlier libraries.

**Nat: 46 readable, 83 helpers** (`9b93b45`). `nat.bend` is the library
everything leans on and it is mostly plumbing: 129 laws, 46 of them the
interface. Readable are the definitional recursions, the ring, the subtraction
laws, the comparison primitives, the successor facts, the division surface,
positivity and the gcd interface. Helpers are the `ci1`..`ci10`
cross-multiplication steps (18), the `Cmp` constructor-discrimination levers, 21
derived comparison rules, the `divmod.go`/`gcd.go`/`slack` machinery, the
sub/cross/evidence plumbing, the rearrangements and `gcd.divides_lt`/`gt` (the
two sign branches of the readable `gcd_divides`).

Three more script bugs, all three found by measurement rather than by reading:

1. **The rebuild dropped interleaved defs.** Building the new library as
   `header + kept units` silently lost every def sitting between two moved laws.
   `nat.bend` has five of them (`type Nat.Div`, `Nat.divides`,
   `Nat.divides_both`, `Nat.gcd.go`, `Nat.gcd`), so `Nat.gcd` became undefined:
   `expected : a defined name / observed : Nat.gcd` at `gcd_scale`, in *both*
   output files. The rebuild is now a deletion of the moved spans from the
   original text, so nothing else can be lost.
2. **A unit's span ran to the next law, not to the end of its own body.** So the
   five defs above were swallowed a second time (only `Cmp.flip` survived), and
   the patch that fixed it crashed first with `KeyError: 'a'` -- the parsed units
   carry `s`/`e`, not the declaration index. A law body is its declaration line
   plus its indented continuations, and the body now ends at the first line back
   at column 0. Verified afterwards by counting: six `def`/`type` lines still in
   `nat.bend`, and the file checks.
3. **The reference rewriter used the spec's alias, not each importer's.**
   `nat_proofs.bend` imports nat as `NL` -- every other file uses `N` -- so its
   282 references, the fill declarations included, still pointed at laws that had
   moved, and **every gate went red** (`expected : '->' (a def with no return
   type fills a law; no law named NL.add_exchange is in scope)`). The rewriter now
   reads the alias out of the importer's own import line:
   `def NLH.add_exchange(a, b, c)` and `import ./nat_helpers.bend as NLH`.

Bug 3 is the interesting one, because of what it says about the acceptance test.
With the alias wrong, `nat.bend` still read 46 and `nat_helpers.bend` still read
129 -- the count invariant held while the library was unusable. The counts and
the gates are independent tests and both are needed; the counts catch a mis-wired
import graph, the gates catch a mis-aliased fill.

**Counts, measured.** `nat.bend` 129 -> 46, `nat_helpers.bend` 129 (= 46
imported + its own 83); `rat.bend` 229 -> 201, `rat_helpers.bend` 229 (= 201 +
28); `tower.bend` 244 -> 242, `tower_helpers.bend` 244 (= 242 + 2). Every
consumer byte-identical: int 19, int_helpers 32, qrat 265, qext 34.
(`int.bend` imports only `Base` -- `Int` is built from builtin Nat operations --
so the int counts are untouched by a nat change.)

All ten gates check: the six `*_proofs.bend` files, `probe.bend`,
`probe.payoff.bend`, both tower probes, and `scratch.bend` still prints its
inversion triple.

**Two libraries need no helper file, and that is a measurement.** `qext.bend`
has two laws and both are the headline commutativity; `qrat.bend` has 36 and
every one is the layer's algebra -- ring, conjugation, norm, division, the
zero-product law, the d = 4 boundary pair -- with the sign splits being the
theorems themselves, exactly as in rat. There is no `qext_helpers.bend` and no
`qrat_helpers.bend`, and the README says so explicitly rather than leaving it to
be inferred.

**Where the three tiers ended up:** int 19/13, rat 40/28, tower 13/2, nat 46/83,
qrat 36/0, qext 2/0 -- 156 readable laws, 126 helpers, 282 in total, which is the
number the repo had before the split.

## Round forty-five -- The product's two facts are one induction, and the fuel becomes a parameter

Rounds forty-one and forty-two left the multiplication chain as three laws in order:
`mul.clean` -> `mul.depth` -> `mul.fuel.ext`. That order is a cycle, and the fill
found it before a proof would have.

**The cycle.** `mul.depth`'s Ext/Ext arm has a recursive call whose first operand is
a *product*: `mul(g, mul(g, ix, iy), dx)`. Proving that call needs
`clean(mul(g, ix, iy))`, which is `mul.clean`'s conclusion. And `mul.clean`'s
Ext/Ext arm needs the *depths* of the four sub-products -- they are the equal-depth
hypothesis `add.clean` takes, and the raw material of the result's own level
relations -- which is `mul.depth`'s conclusion. Neither law comes first.

**What comes first is the pair.** `Tower.mul.safe` concludes an indexed evidence
type, `Tower.Safe<x, p>`, carrying both facts about a product: `csafe:
Tower.clean(p)` and `hdepth: {Tower.depth(p) == Tower.depth(x)}`. One recursive call
hands back both, so each is in hand exactly where the other is needed, and the two
readable laws are projections of the pair -- one call each, in
`Tower.mul.depth` and `Tower.mul.clean`.

**The mechanism was measured before the proof.** `probe.safe.bend` (untracked, in
the repo root) checked that a law can conclude an indexed user-defined evidence
type, that a fill can build one (`{==}` as the depth field), and that a fill can
project its fields. The first attempt also measured the constraint that shapes the
rest of the file: **a match cannot scrutinize a computed value**. Destructuring a
recursive call's result -- `SafeExt{cs, hd} = s1`, and the same with the call
written inline -- is rejected ("give it its own def"), so the pair is read through
defs that take it as a *parameter* (`Tower.safe.clean`, `Tower.safe.depth`);
matching a parameter is legal, matching a computed value is not. Each recursive
call is therefore written twice, once per half. Nothing is shared, and nothing needs
to be: the fuel bounds the work, and the sub-product is recomputed rather than
named.

**The claim is false at insufficient fuel**, so sufficiency is stated rather than
assumed. At `x` of depth 2 and fuel 1 the arm runs with `g = 0`, all four
sub-products are `mul(0n, ...)` = `Fuel{}`, both coordinates are `add(Fuel{},
Fuel{})` = `Fuel{}`, and the product is `Ext{Fuel{}, Fuel{}, dx}`: depth 1, not 2,
and its cleanliness would need `clean(Fuel{})`, which is `Empty`. The law carries
`hf: {f == 1n+Tower.depth(x)}` -- one level per operand, the fuel the definition's
own recursion consumes. Each recursive call needs its own instance, and the chain is
three links: `hf1` is `hf` with `succ_inj` on both sides, `hf2` replaces
`depth(rx)` by `depth(ix)` through the operand's `hri`, and `hf3` uses the
*sub-product's own* depth fact from the second recursive call (which is why the
pair, and not two separate laws, is what makes the third call provable).

**The fuel has to be a parameter**, which is the second measurement and is
independent of the first. Bend requires a self-call's arguments to read left to
right with each unchanged until one shrinks, and the third call passes a computed
product in the second slot. With the fuel spelled `1n+g` in the conclusion the
checker refuses verbatim:

    a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)

The fuel is the first argument and it is already the smaller one, so nothing before
the product can shrink. As a parameter, `match f: case 1n+g` puts `g` in scope as a
strict subterm of it, the fuel shrinks in the first slot, and every later argument is
free -- which is exactly how `Tower.mul`'s own definition gets away with the
identical call. The readable statement at `1n+Tower.depth(x)` is then the projection
at `f := 1n+Tower.depth(x)` with `hf := {==}`, definitional because
`1n+Tower.depth(x)` *is* `Nat.add(1n, Tower.depth(x))`.

Three of the four fill bugs this round were orientation: `Equal.sym` applied to a
hypothesis the trans already wanted in the given direction, twice, and `Equal.cong`
called with its endpoints in the other order once. The checker names the expected
and observed types and they are exact mirrors, so each is a one-line fix; the habit
worth keeping is that the middle of a `trans` is the first leg's *endpoint*, and
every leg's two ends have to be read off the leg, not off the statement.

**Counts, measured.** `tower.bend` 15 laws (13 readable before this round) and
`tower_helpers.bend` 3 laws plus the type `Tower.Safe`. Every other library is
untouched: nat 46/83, int 19/13, rat 40/28, qrat 36, qext 2.

**All ten gates check**: the six `*_proofs.bend` files, `probe.bend`,
`probe.payoff.bend`, `probe.tower.depth.bend`, `probe.mul.depth.arm.bend`, and
`scratch.bend` still prints its inversion triple. `tower_proofs.bend` runs in 2.8 s
end to end, which is over the one-second rule and is now the slowest of the six;
the arm's four recursive calls written twice are the reason, and the backlogged
fast-path item covers it.

## Round forty-six -- The ring laws need a level invariant, measured before it was written

Step 2's five ring laws are the next unit, and the first probe says they do not go
through as stated. Both halves of that are measurements.

**The closed one.** `Tower.add`'s Ext/Ext arm returns the *first* operand's
radicand. Two depth-1 values with radicands 2 and 3, added one way and then the
other, are equal in both coordinates and differ in the third field:

    - expected : src/tower.Ext{..., src/tower.Base{src/rat.Rat{src/int.Int{3n, 0n}, 2n}}}
    - observed : src/tower.Ext{..., src/tower.Base{src/rat.Rat{src/int.Int{2n, 0n}, 2n}}}

So a same-level swap is not an identity of the representation unless the operands
agree on their radicand, and the agreement the law needs at the top is only the
first of the agreements the *induction* needs.

**The open one.** Stating the law with the agreement it obviously needs -- clean
operands, equal depth, `{rad(x) == rad(y)}` -- gives a true statement that cannot
take an induction step:

    - expected : Probe.Rad(rx)
    - observed : Probe.Rad(ry)

That is the recursive call's sixth argument, at the Ext/Ext arm, where the
re-coordinate obligation is this same law at the coordinates. The context lists
everything in scope: `clean(rx)`, `clean(ix)`, `clean(dx)` and the same for `y`,
`{1n+depth(rx) == 1n+depth(ry)}`, `{dx == dy}`. Each hypothesis relates *one*
operand to its own shape, or relates the two at the top level only; nothing relates
their parts. `Tower.Clean` is per-value evidence, and a pairwise, co-recursive fact
is not something per-value evidence can carry.

**Why this is not a surprise in hindsight.** Round twenty-two's own paragraph on the
explicit radicand parameter says the parameter "keeps the laws free of
shape-agreement hypotheses", because `add(d, x, y)` and `add(d, y, x)` mention one
radicand. Round thirty-nine retired the parameter for good reasons -- the intrinsic
radicand removed a side condition and let `mul` and `add` share one evidence type --
and the obligation moved into the laws, where it is unstatable. The plan's Step 2 now
records the fork (a unary `Tower.At<x, c>` level-membership evidence; a pairwise
`Tower.Same<x, y>` bisimulation; or restoring the parameter), each needing the
projection defs `re`, `im`, `rad` that round thirty-nine retired as unnecessary for
the operations and which are needed again to *state* an evidence type over operands'
parts.

**Also measured, and a doc fix rather than a proof.** `mul`'s comment says an
exhausted fuel "says the caller's fuel was too small, not that the operands disagreed
about their level", but the definition compares shapes, not radicands: disagreement
is neither `Bad` nor `Fuel`, it is a silently different value. Evidence closes it at
the law level -- a caller who cannot state the operation never builds the value --
and that is the argument for route 1.

**Not blocked.** The identity and negation block and `mul.fuel.ext` are unary
statements: `neg(neg(x)) = x`, `neg(add(x, y)) = add(neg(x), neg(y))` and
`mul(f, x, one(x)) = x` pick the first operand's radicand on both sides, so their
inductions never need a fact about a pair. Those go next.

The measurement lives in `probe.addcomm.bend` (untracked, repo root), which is the
source of both transcripts above.

## Round forty-seven -- The identity block starts, and the evidence problem has a second face

The block after the ring laws is the identity and negation group: `neg_neg`,
`add_neg`, `neg_add`, `mul_neg`, `neg_mul`, `add_zero`, `zero_add`, `mul_one`,
`one_mul`, `mul_zero`. Round forty-six called these unblocked because they are unary
-- no fact about a *pair* of operands -- and that is true as far as it goes. What it
missed is that they are the first tower laws whose proof needs a fact about a
*coefficient*, and the design carries none.

**Landed: `Tower.sub` and `Tower.sub_eq_add_neg`.** `sub` is `add(x, neg(y))` by
definition, exactly as `Rat.sub` is, so its twin law is the definition's unfolding and
its fill is `{==}`. It is the one law of the block that needs nothing of its operands;
`tower.bend` now has sixteen stated laws. `Tower.sub_eq_add_neg` mirrors
`Rat.sub_eq_add_neg`'s name rather than the dotted style, since a def named `sub` is
what it is about.

**Measured: the Rat value laws are stated at spellings.** `Rat.neg_neg` is

    for +c: Cmp
    for +np, +nn, +dp: Nat
    for +e: {c == Nat.cmp(np, nn) : Cmp}
    for +g1: {N.Nat.gcd(Rat.mag(np, nn), 1n+dp) == 1n : Nat}
    {Rat.neg(Rat.neg(Rat{Rat.num(np, nn), 1n+dp})) == Rat{Rat.num(np, nn), 1n+dp} : Rat}

A call at an arbitrary `v` fails on the law's *first* parameter: `expected : Cmp /
observed : src/rat.Rat`. The caller does not get to pass a value at all -- it must
supply the spelling's comparison hypothesis and its parts. There is no
`Rat.neg_neg.arb`.

The split across the library is by what each law needs of its operand:

* *General modulo positivity* (`+px: {Nat.cmp(0n, Rat.denof(x)) == LT{} : Cmp}`):
  `Rat.add_neg`, `Rat.zero_mul`, and the whole `.arb` family -- `add_assoc.arb`,
  `mul_assoc.arb`, `mul_distrib.arb`, `neg_add.arb`. `Rat.add_neg`'s own comment
  records why positivity is not cosmetic: at `xd = 0` the sum's denominator is 0, `mk`
  returns `Rat{Int{0,0}, 0}` there, and no law compares that with `Rat.zero()`.
* *Canonical* (`+fx: {Rat.mk(n, d) == Rat{n, d} : Rat}`): `add_zero`, `zero_add`,
  `mul_one`, `one_mul`.
* *Both*: `mul_zero` wants a positive denominator *and* a `Rat{n, 1+dp}` spelling.
* *Canonical and reduced and positive*: `neg_neg`, as above.

So `Tower.neg.neg`'s Base arm -- `Base{Rat.neg(Rat.neg(v))}` against `Base{v}` for an
arbitrary `v` -- has no law to call. The same is true of the identity laws for a
coefficient that is not in a spelling.

**Two faces, one decision.** The tower's evidence must say the level relation between
operands (round forty-six) *and* the per-coefficient facts (this round). Positivity is
the carryable one: it is a recursive property of a value, so a `Tower`-level evidence
type can hold it, provided the Rat library has positivity versions of the laws the
tower calls. Canonicality is a bridge law away (`mk(n,d) == Rat{n,d}` is exactly what
`fx` hypotheses transport). The routes are recorded in TOWER-PLAN's Step 2 together,
because choosing them separately would mean restating the evidence type twice.

**Why the existing tower laws escaped.** `add.depth`, `add.clean`, `mul.depth`,
`mul.clean` conclude structural facts -- depth reads structure, clean recurses on it --
so no coefficient identity is ever needed. The value laws are the first to need one,
and the ring laws are the first to need a pair.

**Also fixed.** `tower.bend`'s radicand commentary still described the retired
parameter design ("the radicand is an operation *parameter* ... callers pass the level's
own") and still claimed that a call mixing levels returns `Bad`. Only *shapes* are
compared, so it now states the intrinsic design and hands the level discipline to the
laws, where round forty-six measured it belongs.

`probe.negneg.bend` (untracked) is the source of the transcript above.

## Round forty-eight -- The fuel law lands, and three mechanics of the congruence

`Tower.mul.fuel.ext` is proved, and chain (1) of the goal is complete. The statement is
the one round thirty-six pinned, stated at the weaker fuel hypothesis the induction
actually needs:

    law Tower.mul.fuel.ext:
      for +f: Nat
      for +x: T.Tower
      for +y: T.Tower
      for hx: T.Tower.clean(x)
      for hy: T.Tower.clean(y)
      for h: {T.Tower.depth(x) == T.Tower.depth(y) : Nat}
      for hf: {Nat.cmp(T.Tower.depth(x), f) == LT{} : Cmp}
      {T.Tower.mul(f, x, y) == T.Tower.mul(1n+T.Tower.depth(x), x, y) : T.Tower}

**Why the pair law is not enough.** `Tower.Safe` is indexed at `f == 1n+depth(x)` -- the
exact fuel its own call is made at. The fuel law's recursive instances are made at `g`,
which its hypothesis bounds only above, and at a fuel above the threshold the product is
an `Ext` holding `Fuel{}` in its coordinates, whose clean evidence is `Empty` (round
thirty-three's measurement). Clean evidence cannot be transported to a different
spelling of the same value either: `Equal.cong` composes a function over values, and the
transport needed here is a function over the *type* `clean(.)`. So the fuel law is its own
induction, concluding a three-field indexed type in the helper tier:

    type Tower.Above<-x: T.Tower, -f: Nat, -y: T.Tower> is Data:
      AboveExt{cabove: T.Tower.clean(T.Tower.mul(f, x, y)),
               habove: {T.Tower.depth(T.Tower.mul(f, x, y)) == T.Tower.depth(x) : Nat},
               habeq:  {T.Tower.mul(f, x, y)
                        == T.Tower.mul(Nat.add(1n, T.Tower.depth(x)), x, y) : T.Tower}}

`Tower.mul.above` is that induction; `above.clean`, `above.depth` and `above.eq` are
projections through defs that take it as a parameter (a match cannot scrutinize a computed
value -- the pair law's lesson, unchanged); `mul.fuel.ext` is one call to `above.eq`. The
exact-fuel pair stays, because its hypothesis is the one callers of `mul.depth` and
`mul.clean` have.

**The value field's rewrite.** Each recursive instance states its threshold product at
*its own* first operand's level (`1n+depth(rx)` for (rx, ry), `1n+depth(ix)` for (ix, iy)),
while the conclusion uses the outer first operand's level everywhere. Three congruences
carry the goal across those equalities -- two in `mul`'s fuel slot
(`u => mul(u, ix, iy)`, `u => mul(u, mul(g, ix, iy), dx)`) and one in the second slot
(`u => mul(1n+depth(rx), u, dx)`). `probe.cong.bend` (untracked) measured both mechanisms
before the fill: a lambda over a `+`-marked parameter, and a lambda that builds a
constructor, both accepted in `Equal.cong`'s function slot.

**Three mechanics, all measured this round.**

- `Equal.cong` wants its hypothesis in its own `a`-to-`b` direction. Reversed, it fails
  with `expected : {depth(ix) == depth(mul(g, ix, iy))} / observed :
  {depth(mul(g, ix, iy)) == depth(ix)}`, so the third call's fuel transport (`hf3`) wraps
  its congruence in `Equal.sym`.
- Bindings are linear. `hf` is wanted by two recursive instances and by the `hfi`
  transport, and the second use is refused: `expected : hf / observed : hf (consumed more
  than once)`. `+` cannot be written in a *def*'s parameter list (`expected : ':' /
  observed : ')'` at the fill's signature), so the copy is a marked binding in the body:
  `+hf1 = hf`, then three uses of `hf1`. Marked destructuring fields
  (`T.CleanExt{+hxr, ...}`) are reusable, which is how `hxr` reaches three calls in both
  fills.
- Order matters inside a body, not just across arms: with the copy placed after the `hfi`
  block the checker answers `expected : a defined name / observed : hf1`.

**Also measured.** The two long `Nat` transitivity chains (`es`, `et`) are written once as
bindings and handed to both `add.clean` and `add.depth`; the first version inlined them at
each site and was one closing paren short in each, and the parser reports it only at the
*next* statement ("expected : a term / observed : '='"), which cost a read of the region
rather than a guess.

**State.** `tower.bend` 16 readable laws (245 transitive), `tower_helpers.bend` 5 helper
laws (250), README totals 159 readable / 129 helpers / 288; `tower_proofs.bend` 2.67 s
against the one-second rule (the slowest of the six fills, and the reason the fast-path
item stays on the backlog). All ten gates green; `scratch.bend` still prints the `Rat.inv`
triple. The ring laws still wait on round forty-six's level-invariant fork and the identity
block on round forty-seven's coefficient decision.

## Round forty-nine -- Route 2 of the level fork is measured green

Round forty-six recorded three routes out of the level fork and round forty-seven
recorded a second, coefficient-shaped face of the same problem. This round
measured the pairwise route, in `probe.ring.bend` (untracked, root) -- and the
probe checks end to end.

The first spelling was the obvious one: a single declared type `Probe.Same<x, y>`
with a constructor per shape and fields reading the operands' parts through
projections. It died at the consume site: `a declared constructor (unknown:
Probe.SameExt)`. The lesson is not the qualification -- it is that a hypothesis
of a *declared* multi-constructor type cannot be destructured usefully: the
consumer needs the constructor known, and the arms that do not match the
operands' shapes have neither a witness nor a contradiction.

The spelling that works is `Tower.clean`'s: a *computed family*. `def
Probe.same(x: Tower, y: Tower) -> Data` returns `Probe.Same.Base` at a Base pair,
`Probe.Same.Ext<rx, ix, dx, ry, iy, dy>` at an Ext pair, and `Empty` otherwise.
Each returned type has exactly one constructor. So:

- at an Ext/Ext call site the hypothesis reduces to `Same.Ext<...>` and the
  consume site is a one-arm match whose fields -- `sre: Probe.same(rx, ry)`,
  `sim: Probe.same(ix, iy)`, `sd: {dx == dy}` -- are already indexed by the
  operands' parts. **No projection defs are needed**, revising round forty-six's
  guess that routes 1 and 2 both need `re`/`im`/`rad`: the family is applied to
  the parts directly, exactly as `CleanExt`'s `cre: Tower.clean(re)` is.
- the disagreeing arms carry `Empty` and close with `Empty.absurd(goal-type, hs)`
  -- the idiom the `mul.above` fill already uses for the marker arms. A wildcard
  does not work: `case _ _` left the family stuck on a variable and the checker
  asked for `Empty` while seeing `Probe.same(src/tower.Base{a}, y)`.
- a caller can build one: `SameExt{SameBase{}, SameBase{}, {==}}` checks for a
  depth-1 pair with a shared radicand. The Base witness is empty, which is all
  the commutativity laws need, since `Rat.add_comm` and `Rat.mul_comm` are
  unconditional.

Probe.AddComm's Ext/Ext arm then fills from the witness: two recursive
instances, three congruences (re, im, radicand) and a nested two-leg
`Equal.trans`. The first attempt failed on the leg count -- `Equal.trans` takes
exactly two legs, so the outer call's third term must be the final endpoint and
not the inner chain's middle:

    expected : {Ext{add(ry, rx), add(ix, iy), dx} == Ext{add(ry, rx), add(iy, ix), dx}}
    observed : {Ext{add(ry, rx), add(ix, iy), dx} == Ext{add(ry, rx), add(iy, ix), dy}}

Recorded in TOWER-PLAN's Step-2 section. The fork itself is still the user's
call -- this round is the measurement that makes one of the three routes cheap.
