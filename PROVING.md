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
  operators.

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
- Unary `Nat` is O(value) at runtime. Proofs don't care; CAD-sized
  coordinates will. A binary-nat layer is the right next investment.

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
